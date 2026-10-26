#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
centinela_test7d.py - Test de 7 dias para la ventana "liquidaciones en Kamino" (klend v1.25.0).

No usa capital ni firma nada: todo es lectura + simulateTransaction.

  selftest  Valida offsets y el modelo contra mainnet (2 minutos). Correlo primero.
  audit     Tus candidatas: refresca cada obligation con los precios de AHORA (misma matematica
            on-chain via refresh_reserves_batch + refresh_obligation simulados) y las clasifica:
            FANTASMA / BLOQUEADA / ORACULO / NO_RENTABLE / NECESITA_CAPITAL / REAL.
  run       N horas de: censo de TODAS las liquidaciones de klend (logsSubscribe) + vigia que
            detecta oportunidades con tu stack y mide cuantos slots viven antes de que otro las tome.
  report    Metrica binaria: SEGUI / CORTA / EXTENDE.

Entorno:
  HELIUS_API_KEY  obligatoria (o RPC_URL y WS_URL completos)
  PAYER_PUBKEY    tu wallet: solo fee payer de las simulaciones (no se firma nada; necesita algo de SOL)
  JUP_API_KEY     opcional, recomendada (free tier): mide el slippage real de vender el colateral

pip install solders httpx websockets
"""
from __future__ import annotations

import argparse
import asyncio
import base64
import csv
import hashlib
import json
import math
import os
import random
import re
import sqlite3
import struct
import sys
import time
from dataclasses import dataclass, field

try:
    import httpx
except ImportError:  # pragma: no cover
    sys.exit("Falta httpx: pip install httpx")

# ----------------------------------------------------------------------------------------------
# Constantes verificadas contra el codigo de klend v1.25.0 (Kamino-Finance/klend, 18/08/2026).
# Offsets absolutos (incluyen el discriminador de 8 bytes), calculados con offset_of! sobre los
# structs de klend-interface; coinciden con tus offsets validados (2208 y 2256).
# ----------------------------------------------------------------------------------------------
KLEND = "KLend2g3cP87fffoy8q1mQqGKjrxjC8boSyAYavgmjD"
MAIN_MARKET = "7u3HeHxYDLhnCoErrtycNokbQYbWGzLs6JSDqGAv5PfF"
SOL_MINT = "So11111111111111111111111111111111111111112"
JITO_TIP_ACCOUNTS = {
    "96gYZGLnJYVFmbjzopPSU6QiEV5fGqZNyN9nmNhvrZU5", "HFqU5x63VTqvQss8hp11i4wVV8bD44PvwucfZ2bU7gRe",
    "Cw8CFyM9FkoMi7K7Crf6HNQqf4uEMzpKw6QNghXLvLkY", "ADaUMid9yfUytqMBgopwjb2DTLSokTSzL1zt6iGPaS49",
    "DfXygSm4jCyNCybVYYK6DwvWqjKee8pbDmJGcLWNDXjh", "ADuUkR4vqLUMWXxW9gh6D6L8pMSawimctcNZ5pGwDcEt",
    "DttWaMuVvTiduZRnguLF7jNxTgiMBZ1hyAumKUiL2KRL", "3AVi9Tg9Uo68tJfuvoKvqKNWKkC5wPdSSdeBnizKZ6jT",
}
SCALE = 1 << 60                      # Fraction U68F60 (y BigFraction usa la misma escala)
OBLIGATION_LEN, RESERVE_LEN, MARKET_LEN = 3344, 8624, 4664
OB_SLICE, RES_SLICE, MKT_SLICE = 2600, 6976, 3440
LIQUIDATION_CHECKS = 0b0010_0011     # PRICE_LOADED | PRICE_AGE_CHECKED | PRICE_USAGE_ALLOWED
PERM_LIQUIDATE = 1 << 2
ZERO32 = bytes(32)
NULL_PUBKEY = bytes([11, 193, 238, 216, 208, 116, 241, 195, 55, 212, 76, 22, 75, 202, 40, 216,
                     76, 206, 27, 169, 138, 64, 177, 28, 19, 90, 156, 0, 0, 0, 0, 0])
MAX_TX_BYTES = 1232


def _disc(ns: str, name: str) -> bytes:
    return hashlib.sha256(f"{ns}:{name}".encode()).digest()[:8]


DISC_OBLIGATION = _disc("account", "Obligation")
DISC_RESERVE = _disc("account", "Reserve")
DISC_MARKET = _disc("account", "LendingMarket")
IX_REFRESH_BATCH = _disc("global", "refresh_reserves_batch")
IX_REFRESH_OBLIGATION = _disc("global", "refresh_obligation")
IX_LIQ_V1 = _disc("global", "liquidate_obligation_and_redeem_reserve_collateral")
IX_LIQ_V2 = _disc("global", "liquidate_obligation_and_redeem_reserve_collateral_v2")

# ----------------------------------------------------------------------------------------------
# base58 (para data de instrucciones y pubkeys) - sin dependencias
# ----------------------------------------------------------------------------------------------
_B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
_B58MAP = {c: i for i, c in enumerate(_B58)}


def b58decode(s: str) -> bytes:
    n = 0
    for c in s:
        n = n * 58 + _B58MAP[c]
    body = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    return b"\x00" * (len(s) - len(s.lstrip("1"))) + body


def b58encode(b: bytes) -> str:
    n = int.from_bytes(b, "big")
    out = []
    while n:
        n, r = divmod(n, 58)
        out.append(_B58[r])
    return "1" * (len(b) - len(b.lstrip(b"\x00"))) + "".join(reversed(out))


_PK_CACHE: dict[bytes, str] = {}


def pks(b: bytes) -> str:
    s = _PK_CACHE.get(b)
    if s is None:
        s = b58encode(b)
        if len(_PK_CACHE) < 500_000:
            _PK_CACHE[b] = s
    return s


def pkb(s: str) -> bytes:
    b = b58decode(s)
    if len(b) != 32:
        raise ValueError(f"pubkey invalida: {s}")
    return b


# ----------------------------------------------------------------------------------------------
# Decoders
# ----------------------------------------------------------------------------------------------
_U64 = struct.Struct("<Q")
_U32 = struct.Struct("<I")
_U16 = struct.Struct("<H")


def u64(b, o): return _U64.unpack_from(b, o)[0]
def u32(b, o): return _U32.unpack_from(b, o)[0]
def u16(b, o): return _U16.unpack_from(b, o)[0]
def u128(b, o): return int.from_bytes(b[o:o + 16], "little")
def u256(b, o): return int.from_bytes(b[o:o + 32], "little")
def pk(b, o): return bytes(b[o:o + 32])


def _name(raw: bytes) -> str:
    return raw.split(b"\x00", 1)[0].decode("utf-8", "replace")


def oracle_enabled(key: bytes) -> bool:
    return key not in (ZERO32, NULL_PUBKEY)


@dataclass(slots=True)
class EGroup:
    gid: int
    max_bonus: int
    ltv: int
    liq: int
    debt_reserve: bytes


@dataclass(slots=True)
class Market:
    pk: bytes
    name: str
    referral_fee_bps: int
    emergency: int
    price_refresh_trigger: int
    close_factor_pct: int
    insolvency_pct: int
    min_full_liq_usd: int
    max_liq_at_once_usd: int
    egroups: dict
    min_skip_ltv: int
    min_skip_bf: int
    order_exec_enabled: int
    price_liq_disabled: int
    perm_authority: bytes
    perm_ops: int


def decode_market(pkey: bytes, d: bytes) -> Market:
    if d[:8] != DISC_MARKET:
        raise ValueError("no es LendingMarket")
    eg = {}
    for i in range(32):
        o = 200 + 72 * i
        gid = d[o + 2]
        if gid:
            eg[gid] = EGroup(gid, u16(d, o), d[o + 3], d[o + 4], pk(d, o + 8))
    return Market(pkey, _name(d[3248:3280]), u16(d, 120), d[122], d[125], d[126], d[127], u64(d, 128),
                  u64(d, 136), eg, u64(d, 3240), u64(d, 3280), d[3304], d[3307], pk(d, 3400), u64(d, 3432))


@dataclass(slots=True)
class Reserve:
    pk: bytes
    version: int
    lu_slot: int
    price_status: int
    market: bytes
    mint: bytes
    available: int
    borrowed_sf: int
    price_sf: int
    price_ts: int
    decimals: int
    cum_rate: int
    fees_sf: int              # protocol + referrer + pending referrer
    cmint_supply: int
    status: int
    emergency: int
    take_rate_pct: int
    prot_liq_fee_pct: int
    prot_order_fee_pct: int
    ltv_pct: int
    liq_pct: int
    min_bonus: int
    max_bonus: int
    bad_debt_bonus: int
    bf_pct: int
    name: str
    max_age: int
    pyth: bytes
    sb_price: bytes
    sb_twap: bytes
    scope: bytes
    block_price_usage: int
    egroups: tuple
    perm_ops: int
    queued_collateral: int

    @property
    def price(self) -> float:
        return self.price_sf / SCALE

    @property
    def total_liquidity(self) -> float:          # Reserve::total_supply()
        return self.available + (self.borrowed_sf - self.fees_sf) / SCALE

    @property
    def rate(self) -> float:                     # liquidez por cToken
        tl = self.total_liquidity
        if self.cmint_supply == 0 or tl <= 0:
            return 1.0
        return tl / self.cmint_supply

    def usd(self, raw_amount: float) -> float:
        return raw_amount * self.price / (10 ** self.decimals)

    def oracle_accounts(self) -> list:
        """Cuentas de oraculo en el orden de refresh_reserve; None = no configurado (se pasa KLEND)."""
        sb_on = oracle_enabled(self.sb_price)
        return [self.pyth if oracle_enabled(self.pyth) else None,
                self.sb_price if sb_on else None,
                self.sb_twap if (sb_on and oracle_enabled(self.sb_twap)) else None,
                self.scope if oracle_enabled(self.scope) else None]


def decode_reserve(pkey: bytes, d: bytes) -> Reserve:
    if d[:8] != DISC_RESERVE:
        raise ValueError("no es Reserve")
    fees = u128(d, 344) + u128(d, 360) + u128(d, 376)
    queued = u64(d, 6968) if len(d) >= 6976 else 0
    return Reserve(pkey, u64(d, 8), u64(d, 16), d[25], pk(d, 32), pk(d, 128), u64(d, 224), u128(d, 232),
                   u128(d, 248), u64(d, 264), u64(d, 272), u256(d, 296), fees, u64(d, 2592), d[4856], d[4864],
                   d[4870], d[4871], d[4869], d[4872], d[4873], u16(d, 4874), u16(d, 4876), u16(d, 4878),
                   u64(d, 5008), _name(d[5032:5064]), u64(d, 5096), pk(d, 5224), pk(d, 5160), pk(d, 5192),
                   pk(d, 5112), d[5256], tuple(x for x in d[5480:5500] if x), u64(d, 5800), queued)


@dataclass(slots=True)
class Ob:
    pk: bytes
    market: bytes
    owner: bytes
    lu_slot: int
    stale: int
    price_status: int
    deposits: list            # (reserve, cTokens, market_value_sf)
    borrows: list             # (reserve, cum_rate_bsf, borrowed_amount_sf, market_value_sf, bf_adj_mv_sf)
    deposited_sf: int
    bfadv_sf: int
    borrowed_mv_sf: int
    unhealthy_sf: int
    egroup: int
    has_debt: int
    referrer: bytes | None
    n_orders: int

    def reserves(self) -> list:
        seen, out = set(), []
        for r in [d[0] for d in self.deposits] + [b[0] for b in self.borrows]:
            if r not in seen:
                seen.add(r)
                out.append(r)
        return out

    @property
    def stored_margin(self) -> float:
        """(ubv - bfadv)/ubv con los valores GUARDADOS (el criterio de tu parser)."""
        if self.unhealthy_sf == 0:
            return -math.inf if self.bfadv_sf > 0 else 0.0
        return (self.unhealthy_sf - self.bfadv_sf) / self.unhealthy_sf


def decode_obligation(pkey: bytes, d: bytes) -> Ob:
    if d[:8] != DISC_OBLIGATION:
        raise ValueError("no es Obligation")
    deps, bors = [], []
    for i in range(8):
        o = 96 + 136 * i
        r = pk(d, o)
        if r != ZERO32:
            deps.append((r, u64(d, o + 32), u128(d, o + 40)))
    for i in range(5):
        o = 1208 + 200 * i
        r = pk(d, o)
        if r != ZERO32:
            bors.append((r, u256(d, o + 32), u128(d, o + 88), u128(d, o + 104), u128(d, o + 120)))
    ref = pk(d, 2288)
    n_orders = 0
    if len(d) >= 2600:
        n_orders = sum(1 for i in range(2) if d[2344 + 128 * i + 36] != 0)
    return Ob(pkey, pk(d, 32), pk(d, 64), u64(d, 16), d[24], d[25], deps, bors, u128(d, 1192), u128(d, 2208),
              u128(d, 2224), u128(d, 2256), d[2285], d[2287], None if ref == ZERO32 else ref, n_orders)


# ----------------------------------------------------------------------------------------------
# Modelo de salud (misma matematica que refresh_obligation) y economia de la liquidacion
# ----------------------------------------------------------------------------------------------
def model_health(ob: Ob, reserves: dict, market: Market):
    """Recalcula LTV con el estado actual de las reserves. None si falta alguna reserve."""
    eg = market.egroups.get(ob.egroup) if ob.egroup else None
    dep = unh = 0.0
    for r, ctokens, _ in ob.deposits:
        R = reserves.get(r)
        if R is None:
            return None
        v = R.usd(ctokens * R.rate)
        dep += v
        unh += v * (eg.liq if eg else R.liq_pct) / 100
    debt = bfadv = 0.0
    for r, cum_ob, bsf, _, _ in ob.borrows:
        R = reserves.get(r)
        if R is None:
            return None
        amt = bsf / SCALE
        if cum_ob and R.cum_rate > cum_ob:
            amt = amt * R.cum_rate / cum_ob
        v = R.usd(amt)
        debt += v
        bfadv += v * (1.0 if eg else max(1.0, R.bf_pct / 100))
    ratio = bfadv / unh if unh > 0 else (math.inf if bfadv > 0 else 0.0)
    return ratio, dep, debt


def liquidation_bonus(C: Reserve, D: Reserve, max_ltv: float, user_ltv: float, no_bf_ltv: float,
                      emode_max_bps: int) -> float:
    """Espejo de calculate_liquidation_bonus (liquidation_operations.rs)."""
    if no_bf_ltv >= 0.99:
        bd = min(C.bad_debt_bonus, D.bad_debt_bonus) / 1e4
        return max(bd, 1.0 - no_bf_ltv) if no_bf_ltv < 1.0 else bd
    max_b = min(max(C.max_bonus, D.max_bonus), emode_max_bps) / 1e4
    min_b = max(C.min_bonus, D.min_bonus) / 1e4
    b = min(max(min_b, user_ltv - max_ltv), max_b)
    return min(b, 1.0 - no_bf_ltv)


def blockers(ob: Ob, market: Market, reserves: dict) -> list:
    out = []
    if market.price_liq_disabled:
        out.append("liq_por_precio_deshabilitada")
    if market.perm_authority != ZERO32:
        ops = market.perm_ops
        for r in ob.reserves():
            R = reserves.get(r)
            ops |= R.perm_ops if R else 0
        if ops & PERM_LIQUIDATE:
            out.append("mercado_permisionado")
    if market.emergency:
        out.append("mercado_emergencia")
    for r in ob.reserves():
        R = reserves.get(r)
        if R and (R.emergency or R.block_price_usage):
            out.append(f"reserve_{R.name}_bloqueada")
    return out


@dataclass(slots=True)
class Estimate:
    bonus: float
    repay_usd: float
    withdraw_usd: float
    gross_usd: float
    prot_fee_usd: float
    net_before_swap: float
    flash_ok: bool
    capital_limited: bool
    coll: bytes
    debt: bytes
    sell_raw: int              # cantidad de colateral (unidades del mint) a vender
    user_ltv: float
    liq_ltv: float
    haircut_pct: float | None = None
    net_usd: float | None = None


def estimate_liquidation(ob: Ob, reserves: dict, market: Market, capital_usd: float) -> Estimate | None:
    """Usa los valores post-refresh (exactos) de la obligation. Reproduce la seleccion de reserves
    (deuda con mayor borrow factor, colateral con menor liquidation threshold), close factor,
    umbral de liquidacion total, tope por liquidacion, bonus y fee de protocolo."""
    dv = ob.deposited_sf / SCALE
    bfadv = ob.bfadv_sf / SCALE
    if dv <= 0 or bfadv <= 0 or not ob.deposits or not ob.borrows:
        return None
    user_ltv, max_ltv, no_bf = bfadv / dv, (ob.unhealthy_sf / SCALE) / dv, (ob.borrowed_mv_sf / SCALE) / dv
    eg = market.egroups.get(ob.egroup) if ob.egroup else None
    for r in ob.reserves():
        if r not in reserves:
            return None

    def bf(r):
        return 1.0 if eg else max(1.0, reserves[r].bf_pct / 100)

    def lt(r):
        return eg.liq if eg else reserves[r].liq_pct

    bors = [(b[0], b[3] / SCALE) for b in ob.borrows]
    el_b = [b for b in bors if b[1] >= market.min_skip_bf] or bors
    debt_r, debt_mv = max(el_b, key=lambda b: (bf(b[0]), b[1]))
    deps = [(d[0], d[2] / SCALE) for d in ob.deposits if lt(d[0]) > 0]
    if not deps:
        return None
    el_d = [d for d in deps if d[1] >= market.min_skip_ltv] or deps
    coll_r, coll_mv = min(el_d, key=lambda d: (lt(d[0]), -d[1]))
    C, D = reserves[coll_r], reserves[debt_r]
    emax = 65535
    if eg and ob.egroup in C.egroups and ob.egroup in D.egroups:
        if not (eg.max_bonus > C.max_bonus or eg.max_bonus > D.max_bonus or eg.max_bonus == 0):
            emax = eg.max_bonus
    bonus = max(0.0, liquidation_bonus(C, D, max_ltv, user_ltv, no_bf, emax))
    if debt_mv < market.min_full_liq_usd:
        repay = debt_mv
    else:
        cf = 1.0 if user_ltv > market.insolvency_pct / 100 else market.close_factor_pct / 100
        repay = min((ob.borrowed_mv_sf / SCALE) * cf, debt_mv, market.max_liq_at_once_usd)   # tope 0 = nada
    withdraw = repay * (1 + bonus)
    if withdraw > coll_mv:
        repay, withdraw = coll_mv / (1 + bonus), coll_mv
    # colateral redimible ahora (si no alcanza, te llevas cTokens: no hay flash loan posible)
    redeemable = C.usd(max(0.0, C.available - C.queued_collateral * C.rate))
    flash_ok = redeemable >= withdraw
    capital_limited = False
    if not flash_ok and repay > capital_usd:
        k = capital_usd / repay
        repay, withdraw, capital_limited = repay * k, withdraw * k, True
    gross = withdraw - repay
    fee = gross * C.prot_liq_fee_pct / 100
    sell_usd = withdraw - fee
    sell_raw = int(sell_usd / C.price * 10 ** C.decimals) if C.price > 0 else 0
    return Estimate(bonus, repay, withdraw, gross, fee, gross - fee, flash_ok, capital_limited, coll_r, debt_r,
                    sell_raw, user_ltv, max_ltv)


# ----------------------------------------------------------------------------------------------
# RPC (Helius) con rate limit y contador de creditos
# ----------------------------------------------------------------------------------------------
class RpcError(Exception):
    pass


class Bucket:
    def __init__(self, rate: float):
        self.rate, self.tokens, self.t = rate, rate, time.monotonic()
        self.lock = asyncio.Lock()

    async def take(self):
        async with self.lock:
            while True:
                now = time.monotonic()
                self.tokens = min(self.rate, self.tokens + (now - self.t) * self.rate)
                self.t = now
                if self.tokens >= 1:
                    self.tokens -= 1
                    return
                await asyncio.sleep((1 - self.tokens) / self.rate)


class Rpc:
    def __init__(self, url: str, rps: float):
        self.url = url
        self.client = httpx.AsyncClient(timeout=45)
        self.bucket = Bucket(rps)
        self.credits = 0
        self.calls: dict[str, int] = {}

    async def call(self, method: str, params: list, credits: int = 1):
        last = None
        for attempt in range(6):
            await self.bucket.take()
            try:
                r = await self.client.post(self.url, json={"jsonrpc": "2.0", "id": 1, "method": method,
                                                           "params": params})
                self.credits += credits
                self.calls[method] = self.calls.get(method, 0) + 1
                if r.status_code == 429 or r.status_code >= 500:
                    last = f"HTTP {r.status_code}"
                    await asyncio.sleep(0.6 * (attempt + 1))
                    continue
                j = r.json()
                if "error" in j:
                    raise RpcError(f"{method}: {j['error']}")
                return j["result"]
            except (httpx.TransportError, httpx.TimeoutException, json.JSONDecodeError) as e:
                last = repr(e)
                await asyncio.sleep(0.6 * (attempt + 1))
        raise RpcError(f"{method}: {last}")

    async def slot(self) -> int:
        return await self.call("getSlot", [{"commitment": "processed"}])

    async def multiple(self, keys: list[str], data_slice: tuple | None = None) -> dict:
        out = {}
        for i in range(0, len(keys), 100):
            chunk = keys[i:i + 100]
            cfg = {"encoding": "base64", "commitment": "confirmed"}
            if data_slice:
                cfg["dataSlice"] = {"offset": data_slice[0], "length": data_slice[1]}
            res = await self.call("getMultipleAccounts", [chunk, cfg])
            for k, v in zip(chunk, res["value"]):
                out[k] = base64.b64decode(v["data"][0]) if v else None
        return out

    async def program_accounts(self, filters: list, data_slice: tuple | None = None,
                               changed_since: int | None = None) -> list:
        out = []
        async for page in self.program_accounts_pages(filters, data_slice, changed_since):
            out.extend(page)
        return out

    async def program_accounts_pages(self, filters: list, data_slice: tuple | None = None,
                                     changed_since: int | None = None):
        """getProgramAccountsV2 paginado (1 credito/pagina en Helius), pagina por pagina.
        Fallback a getProgramAccounts (10 creditos, sin paginar) si V2 no existe en tu RPC."""
        cfg = {"encoding": "base64", "filters": filters, "limit": 10000, "commitment": "confirmed"}
        if data_slice:
            cfg["dataSlice"] = {"offset": data_slice[0], "length": data_slice[1]}
        if changed_since is not None:
            cfg["changedSinceSlot"] = changed_since
        key = None
        try:
            while True:
                c = dict(cfg)
                if key:
                    c["paginationKey"] = key
                res = await self.call("getProgramAccountsV2", [KLEND, c])
                accs = res.get("accounts", [])
                yield [(a["pubkey"], base64.b64decode(a["account"]["data"][0])) for a in accs]
                key = res.get("paginationKey")
                if not accs or not key:
                    return
        except RpcError as e:
            if changed_since is not None or key is not None:
                raise
            log(f"getProgramAccountsV2 no disponible ({e}); uso getProgramAccounts (10 creditos)")
            c = {k: v for k, v in cfg.items() if k not in ("limit", "changedSinceSlot")}
            res = await self.call("getProgramAccounts", [KLEND, c], credits=10)
            yield [(a["pubkey"], base64.b64decode(a["account"]["data"][0])) for a in res]

    async def simulate(self, tx_b64: str, addresses: list[str]):
        cfg = {"encoding": "base64", "sigVerify": False, "replaceRecentBlockhash": True,
               "commitment": "processed", "accounts": {"encoding": "base64", "addresses": addresses}}
        res = await self.call("simulateTransaction", [tx_b64, cfg])
        v = res["value"]
        accs = [base64.b64decode(a["data"][0]) if a else None for a in (v.get("accounts") or [])]
        return res["context"]["slot"], v.get("err"), v.get("logs") or [], accs


def log(*a):
    print(time.strftime("%Y-%m-%d %H:%M:%S"), *a, flush=True)


# ----------------------------------------------------------------------------------------------
# Construccion de transacciones de simulacion (no se firman)
# ----------------------------------------------------------------------------------------------
class TxBuilder:
    def __init__(self, payer: str):
        from solders.compute_budget import set_compute_unit_limit
        from solders.hash import Hash
        from solders.instruction import AccountMeta, Instruction
        from solders.message import MessageV0
        from solders.pubkey import Pubkey
        from solders.signature import Signature
        from solders.transaction import VersionedTransaction
        self.P, self.AM, self.IX, self.Msg, self.H = Pubkey, AccountMeta, Instruction, MessageV0, Hash
        self.Sig, self.VTx, self.cu = Signature, VersionedTransaction, set_compute_unit_limit
        self.payer = Pubkey.from_string(payer)
        self.klend = Pubkey.from_string(KLEND)
        self._pk: dict[bytes, object] = {}

    def P_(self, b: bytes):
        p = self._pk.get(b)
        if p is None:
            p = self.P.from_bytes(b)
            self._pk[b] = p
        return p

    def refresh_batch_ix(self, reserves: list[Reserve]):
        metas = []
        for R in reserves:
            metas.append(self.AM(self.P_(R.pk), False, True))
            metas.append(self.AM(self.P_(R.market), False, False))
            for o in R.oracle_accounts():
                metas.append(self.AM(self.P_(o) if o else self.klend, False, False))
        return self.IX(self.klend, IX_REFRESH_BATCH + b"\x00", metas)

    def refresh_obligation_ix(self, ob: Ob, market: Market, reserves: dict):
        metas = [self.AM(self.P_(ob.market), False, False), self.AM(self.P_(ob.pk), False, True)]
        metas += [self.AM(self.P_(d[0]), False, True) for d in ob.deposits]
        metas += [self.AM(self.P_(b[0]), False, True) for b in ob.borrows]
        if ob.referrer:
            first, pad = [], []
            for b in ob.borrows:
                pda, _ = self.P.find_program_address([b"referrer_acc", ob.referrer, b[0]], self.klend)
                R = reserves.get(b[0])
                takes = (R is None or R.take_rate_pct > 0) and market.referral_fee_bps > 0
                (first if takes else pad).append(self.AM(pda, False, True))
            metas += first + pad
        return self.IX(self.klend, IX_REFRESH_OBLIGATION, metas)

    def tx_b64(self, ixs: list) -> str | None:
        msg = self.Msg.try_compile(self.payer, [self.cu(1_400_000)] + ixs, [], self.H.default())
        raw = bytes(self.VTx.populate(msg, [self.Sig.default()]))
        return base64.b64encode(raw).decode() if len(raw) <= MAX_TX_BYTES else None


def sim_error_text(err, logs: list) -> str:
    for line in reversed(logs):
        m = re.search(r"Error Code: (\w+)", line)
        if m:
            return m.group(1)
    return json.dumps(err)[:120]


# ----------------------------------------------------------------------------------------------
# Estado compartido + carga inicial
# ----------------------------------------------------------------------------------------------
@dataclass
class Opp:
    ob: bytes
    market: bytes
    first_slot: int
    first_ts: float
    kind: str
    est_open: float
    last_slot: int
    last_check: float = 0.0
    capturable: int = 0
    est_at_L: float | None = None
    db_id: int | None = None


@dataclass
class State:
    markets: dict = field(default_factory=dict)
    reserves: dict = field(default_factory=dict)
    obligations: dict = field(default_factory=dict)
    ratio: dict = field(default_factory=dict)
    debt: dict = field(default_factory=dict)
    warm: set = field(default_factory=set)
    candidates: dict = field(default_factory=dict)      # ob -> prioridad
    cooldown: dict = field(default_factory=dict)        # ob -> monotonic hasta
    open_opps: dict = field(default_factory=dict)
    recent_liq: dict = field(default_factory=dict)      # ob -> slot
    recently_closed: dict = field(default_factory=dict)  # ob -> (Opp, monotonic) para la carrera con el censo
    bad_reserves: dict = field(default_factory=dict)
    ws_bytes: int = 0
    last_slot: int = 0
    stop: bool = False
    stats: dict = field(default_factory=lambda: {"liq_ok": 0, "liq_fail": 0, "sims": 0, "opps": 0, "capt": 0})


async def load_markets_reserves(rpc: Rpc, st: State):
    for k, d in await rpc.program_accounts([{"dataSize": MARKET_LEN}], (0, MKT_SLICE)):
        try:
            st.markets[pkb(k)] = decode_market(pkb(k), d)
        except ValueError:
            pass
    for k, d in await rpc.program_accounts([{"dataSize": RESERVE_LEN}], (0, RES_SLICE)):
        try:
            st.reserves[pkb(k)] = decode_reserve(pkb(k), d)
        except ValueError:
            pass
    log(f"mercados: {len(st.markets)} | reserves: {len(st.reserves)}")


def ob_filters(market: str | None = None, has_debt: bool = True) -> list:
    f = [{"dataSize": OBLIGATION_LEN}, {"memcmp": {"offset": 0, "bytes": b58encode(DISC_OBLIGATION)}}]
    if has_debt:
        f.append({"memcmp": {"offset": 2287, "bytes": b58encode(b"\x01")}})
    if market:
        f.append({"memcmp": {"offset": 32, "bytes": market}})
    return f


async def load_obligations(rpc: Rpc, st: State, markets: list[str] | None):
    total = 0
    for m in (markets or [None]):
        async for page in rpc.program_accounts_pages(ob_filters(m), (0, OB_SLICE)):
            for k, d in page:
                try:
                    ob = decode_obligation(pkb(k), d)
                except ValueError:
                    continue
                st.obligations[ob.pk] = ob
                total += 1
            if total and total % 50_000 < len(page):
                log(f"  ... {total} obligations")
    log(f"obligations con deuda cargadas: {total}")


# ----------------------------------------------------------------------------------------------
# Simulaciones: refrescar precios de reserves y refrescar obligations exactas
# ----------------------------------------------------------------------------------------------
async def sim_refresh_reserves(rpc: Rpc, tb: TxBuilder, st: State, reserve_keys: list[bytes]) -> int:
    """Refresca (en simulacion) las reserves y guarda su post-estado. Devuelve el slot."""
    todo = [st.reserves[r] for r in reserve_keys if r in st.reserves and r not in st.bad_reserves]
    todo.sort(key=lambda R: R.market)
    slot = 0

    async def run(batch: list[Reserve]):
        nonlocal slot
        if not batch:
            return
        b64 = tb.tx_b64([tb.refresh_batch_ix(batch)])
        if b64 is None and len(batch) > 1:
            h = len(batch) // 2
            await run(batch[:h])
            await run(batch[h:])
            return
        if b64 is None:
            st.bad_reserves[batch[0].pk] = "tx_demasiado_grande"
            return
        s, err, logs, accs = await rpc.simulate(b64, [pks(R.pk) for R in batch])
        st.stats["sims"] += 1
        if err:
            if len(batch) == 1:
                st.bad_reserves[batch[0].pk] = sim_error_text(err, logs)
                return
            h = len(batch) // 2
            await run(batch[:h])
            await run(batch[h:])
            return
        slot = max(slot, s)
        for R, d in zip(batch, accs):
            if d:
                st.reserves[R.pk] = decode_reserve(R.pk, d)

    for i in range(0, len(todo), 16):
        await run(todo[i:i + 16])
    return slot


async def sim_refresh_obligation(rpc: Rpc, tb: TxBuilder, st: State, ob: Ob):
    """Devuelve (slot, ob_post, error). Actualiza las reserves con el post-estado."""
    market = st.markets.get(ob.market)
    rs = ob.reserves()
    if market is None or any(r not in st.reserves for r in rs):
        return 0, None, "reserve_o_mercado_desconocido"
    bad = [st.bad_reserves[r] for r in rs if r in st.bad_reserves]
    if bad:
        return 0, None, f"reserve_no_refrescable:{bad[0]}"
    reserves = [st.reserves[r] for r in rs]
    b64 = tb.tx_b64([tb.refresh_batch_ix(reserves), tb.refresh_obligation_ix(ob, market, st.reserves)])
    if b64 is None:
        return 0, None, "tx_demasiado_grande"
    slot, err, logs, accs = await rpc.simulate(b64, [pks(ob.pk)] + [pks(r) for r in rs])
    st.stats["sims"] += 1
    if err:
        return slot, None, sim_error_text(err, logs)
    for R, d in zip(reserves, accs[1:]):
        if d:
            st.reserves[R.pk] = decode_reserve(R.pk, d)
    return slot, decode_obligation(ob.pk, accs[0]), None


# ----------------------------------------------------------------------------------------------
# Jupiter: cuanto cuesta de verdad vender el colateral (opcional)
# ----------------------------------------------------------------------------------------------
class Jup:
    def __init__(self, key: str | None):
        self.key = key
        self.client = httpx.AsyncClient(timeout=20) if key else None
        self.cache: dict = {}
        self.bucket = Bucket(0.9)

    async def haircut(self, C: Reserve, D: Reserve, sell_raw: int) -> float | None:
        """Fraccion perdida al vender sell_raw de C por D vs el precio de oraculo. None si no se puede medir."""
        if C.mint == D.mint:
            return 0.0
        if not self.key or sell_raw <= 0:
            return None
        bucket_ = int(math.log2(max(sell_raw, 1)) * 4)
        ck = (C.mint, D.mint, bucket_)
        hit = self.cache.get(ck)
        if hit and time.time() - hit[0] < 120:
            return hit[1]
        await self.bucket.take()
        try:
            r = await self.client.get("https://api.jup.ag/swap/v2/order",
                                      params={"inputMint": pks(C.mint), "outputMint": pks(D.mint),
                                              "amount": str(sell_raw)},
                                      headers={"x-api-key": self.key})
            j = r.json()
            out = int(j["outAmount"])
            hc = 1.0 - D.usd(out) / C.usd(sell_raw)
        except Exception:
            hc = 1.0                        # sin ruta = colateral invendible en la practica
        self.cache[ck] = (time.time(), hc)
        return hc


# ----------------------------------------------------------------------------------------------
# SQLite
# ----------------------------------------------------------------------------------------------
SCHEMA = """
CREATE TABLE IF NOT EXISTS liquidations(sig TEXT, idx INT, slot INT, ts REAL, reason TEXT, bonus_bps INT,
  ltv_pct REAL, liq_ltv_pct REAL, liquidator TEXT, fee_payer TEXT, obligation TEXT, market TEXT,
  repay_mint TEXT, withdraw_mint TEXT, repay_raw INT, withdraw_raw INT, prot_fee_raw INT, repay_usd REAL,
  profit_usd REAL, fee_lamports INT, tip_lamports INT, cpi INT, outer_program TEXT, seen_by_us INT,
  lead_slots INT, PRIMARY KEY(sig, idx));
CREATE TABLE IF NOT EXISTS attempts(sig TEXT PRIMARY KEY, slot INT, ts REAL, ok INT, err TEXT, n_pnl INT);
CREATE TABLE IF NOT EXISTS opportunities(id INTEGER PRIMARY KEY AUTOINCREMENT, obligation TEXT, market TEXT,
  kind TEXT, first_slot INT, first_ts REAL, last_slot INT, close_slot INT, close_reason TEXT, liquidator TEXT,
  est_open_usd REAL, est_at_L_usd REAL, capturable INT, bonus_bps REAL, repay_usd REAL, flash_ok INT,
  haircut_pct REAL, is_main INT);
CREATE TABLE IF NOT EXISTS audit(obligation TEXT PRIMARY KEY, market TEXT, market_name TEXT, klass TEXT,
  stored_stale INT, stored_age_h REAL, stored_margin REAL, fresh_ratio REAL, deposit_usd REAL, debt_usd REAL,
  bonus_bps REAL, net_usd REAL, flash_ok INT, haircut_pct REAL, detail TEXT, ts REAL);
CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v TEXT);
"""


def db_open(path: str) -> sqlite3.Connection:
    con = sqlite3.connect(path)
    con.executescript(SCHEMA)
    return con


def meta_set(con, k, v):
    con.execute("INSERT OR REPLACE INTO meta VALUES(?,?)", (k, json.dumps(v)))
    con.commit()


def meta_get(con, k, default=None):
    r = con.execute("SELECT v FROM meta WHERE k=?", (k,)).fetchone()
    return json.loads(r[0]) if r else default


# ----------------------------------------------------------------------------------------------
# Censo: parseo de logs y transacciones de liquidacion
# ----------------------------------------------------------------------------------------------
RE_REASON = re.compile(r"eligible for liquidation because of (\w+)(?:\((\d+)\))? with liquidation bonus: (\d+)\s*bps")
RE_LTV = re.compile(r"Obligation is eligible for liquidation, borrowed value.*?LTV: ([\d.]+)%/([\d.]+)%")
RE_PNL = re.compile(r"pnl: Liquidator repaid (\d+) and withdrew (\d+) collateral with fees (\d+)")
ATTEMPT_MARK = "Liquidating liquidation_close_factor_pct"


def parse_liq_logs(logs: list[str]) -> list[dict]:
    recs, pending_ltv = [], None
    for line in logs:
        m = RE_LTV.search(line)
        if m:
            pending_ltv = (float(m.group(1)), float(m.group(2)))
            continue
        m = RE_REASON.search(line)
        if m:
            recs.append({"reason": m.group(1), "bonus_bps": int(m.group(3)),
                         "ltv": pending_ltv[0] if pending_ltv else None,
                         "liq_ltv": pending_ltv[1] if pending_ltv else None})
            pending_ltv = None
            continue
        m = RE_PNL.search(line)
        if m:
            target = next((r for r in recs if "repay_raw" not in r), None)
            if target is None:
                target = {"reason": None, "bonus_bps": None, "ltv": None, "liq_ltv": None}
                recs.append(target)
            target.update(repay_raw=int(m.group(1)), withdraw_raw=int(m.group(2)), fee_raw=int(m.group(3)))
    return [r for r in recs if "repay_raw" in r]


def parse_liq_ixs(tx: dict) -> list[dict]:
    msg, meta = tx["transaction"]["message"], tx["meta"]
    la = meta.get("loadedAddresses") or {}
    keys = msg["accountKeys"] + la.get("writable", []) + la.get("readonly", [])
    inner = {g["index"]: g["instructions"] for g in (meta.get("innerInstructions") or [])}
    out = []
    for i, top in enumerate(msg["instructions"]):
        for ix, is_cpi in [(top, False)] + [(x, True) for x in inner.get(i, [])]:
            if keys[ix["programIdIndex"]] != KLEND:
                continue
            data = b58decode(ix["data"])
            if data[:8] not in (IX_LIQ_V1, IX_LIQ_V2) or len(ix["accounts"]) < 9:
                continue
            a = [keys[j] for j in ix["accounts"]]
            out.append({"liquidator": a[0], "obligation": a[1], "market": a[2], "repay_reserve": a[4],
                        "repay_mint": a[5], "withdraw_reserve": a[7], "withdraw_mint": a[8], "cpi": int(is_cpi),
                        "outer_program": keys[top["programIdIndex"]]})
    tip = 0
    for j, k in enumerate(keys):
        if k in JITO_TIP_ACCOUNTS and j < len(meta["postBalances"]):
            tip += max(0, meta["postBalances"][j] - meta["preBalances"][j])
    for o in out:
        o.update(fee_payer=keys[0], fee=meta.get("fee", 0), tip=tip)
    return out


# ----------------------------------------------------------------------------------------------
# Comando: selftest
# ----------------------------------------------------------------------------------------------
def env_urls():
    key = os.environ.get("HELIUS_API_KEY")
    rpc = os.environ.get("RPC_URL") or (f"https://mainnet.helius-rpc.com/?api-key={key}" if key else None)
    ws = os.environ.get("WS_URL") or (f"wss://mainnet.helius-rpc.com/?api-key={key}" if key else None)
    if not rpc:
        sys.exit("Defini HELIUS_API_KEY (o RPC_URL y WS_URL).")
    return rpc, ws


def need_payer() -> str:
    p = os.environ.get("PAYER_PUBKEY")
    if not p:
        sys.exit("Defini PAYER_PUBKEY (tu wallet; solo paga la simulacion, no se firma nada).")
    return p


async def cmd_selftest(args):
    rpc_url, ws_url = env_urls()
    rpc, tb, st = Rpc(rpc_url, args.rps), TxBuilder(need_payer()), State()
    log("slot:", await rpc.slot())
    await load_markets_reserves(rpc, st)
    if not st.markets or not st.reserves:
        sys.exit("FALLO: no pude leer mercados/reserves (discriminador o tamano cambiaron?)")
    names = sorted((m.name or pks(k)[:8]) for k, m in st.markets.items())
    log("mercados:", ", ".join(names[:25]), "..." if len(names) > 25 else "")
    mkt = MAIN_MARKET if pkb(MAIN_MARKET) in st.markets else pks(next(iter(st.markets)))
    obs = []
    res = await rpc.call("getProgramAccountsV2", [KLEND, {"encoding": "base64", "filters": ob_filters(mkt),
                                                          "dataSlice": {"offset": 0, "length": OB_SLICE},
                                                          "limit": 400}])
    for a in res.get("accounts", []):
        obs.append(decode_obligation(pkb(a["pubkey"]), base64.b64decode(a["account"]["data"][0])))
    random.shuffle(obs)
    errs, n = [], 0
    for ob in obs[:args.n]:
        slot, post, err = await sim_refresh_obligation(rpc, tb, st, ob)
        if err or post is None or post.unhealthy_sf == 0:
            continue
        mh = model_health(ob, st.reserves, st.markets[ob.market])
        if not mh:
            continue
        exact = post.bfadv_sf / post.unhealthy_sf
        errs.append(abs(mh[0] - exact) / exact)
        n += 1
    if not errs:
        sys.exit("FALLO: ninguna simulacion valida. Revisa PAYER_PUBKEY (debe existir y tener SOL).")
    errs.sort()
    log(f"modelo vs refresh on-chain en {n} obligations: error mediano {errs[len(errs) // 2]:.2e}, "
        f"max {errs[-1]:.2e}  ->  {'OK' if errs[-1] < 5e-3 else 'REVISAR (modelo desalineado)'}")
    if ws_url:
        import websockets
        t0, nbytes, nmsg = time.time(), 0, 0
        async with websockets.connect(ws_url, ping_interval=20, max_size=2 ** 23) as ws:
            await ws.send(json.dumps({"jsonrpc": "2.0", "id": 1, "method": "logsSubscribe",
                                      "params": [{"mentions": [KLEND]}, {"commitment": "confirmed"}]}))
            while time.time() - t0 < 20:
                try:
                    raw = await asyncio.wait_for(ws.recv(), timeout=5)
                except asyncio.TimeoutError:
                    continue
                nbytes += len(raw)
                nmsg += 1
        mb_day = nbytes / 1e6 * 86400 / 20
        log(f"websocket logs klend: {nmsg} msgs en 20s -> ~{mb_day:.0f} MB/dia -> ~{mb_day * 20:,.0f} creditos/dia")
    jk = os.environ.get("JUP_API_KEY")
    if jk:
        j = Jup(jk)
        sol = next((R for R in st.reserves.values() if pks(R.mint) == SOL_MINT and R.price > 0), None)
        usdc = next((R for R in st.reserves.values() if pks(R.mint).startswith("EPjFWdd5") and R.price > 0), None)
        if sol and usdc:
            hc = await j.haircut(sol, usdc, 10 * 10 ** 9)
            log(f"jupiter OK: vender 10 SOL cuesta {hc * 100:.3f}% vs oraculo" if hc is not None else "jupiter FALLO")
    log(f"creditos usados en el selftest: ~{rpc.credits}")


# ----------------------------------------------------------------------------------------------
# Comando: audit
# ----------------------------------------------------------------------------------------------
def read_candidates(path: str) -> list[str]:
    out = []
    with open(path, newline="") as f:
        for row in csv.reader(f):
            for cell in row:
                cell = cell.strip()
                if 32 <= len(cell) <= 44 and all(c in _B58MAP for c in cell):
                    out.append(cell)
                    break
    return list(dict.fromkeys(out))


async def classify(rpc, tb, st, jup, ob: Ob, cur_slot: int, capital: float, min_profit: float,
                   tx_cost: float) -> dict:
    market = st.markets.get(ob.market)
    row = {"obligation": pks(ob.pk), "market": pks(ob.market), "market_name": market.name if market else "?",
           "stored_stale": ob.stale, "stored_age_h": (cur_slot - ob.lu_slot) * 0.4 / 3600 if cur_slot else None,
           "stored_margin": ob.stored_margin, "fresh_ratio": None, "deposit_usd": None, "debt_usd": None,
           "bonus_bps": None, "net_usd": None, "flash_ok": None, "haircut_pct": None, "detail": ""}
    slot, post, err = await sim_refresh_obligation(rpc, tb, st, ob)
    if err:
        row.update(klass="REFRESH_FALLA", detail=err)
        return row
    row["deposit_usd"] = post.deposited_sf / SCALE
    row["debt_usd"] = post.borrowed_mv_sf / SCALE
    row["fresh_ratio"] = post.bfadv_sf / post.unhealthy_sf if post.unhealthy_sf else None
    if post.bfadv_sf < post.unhealthy_sf or post.bfadv_sf == 0:
        row.update(klass="FANTASMA", detail="sana con precios actuales")
        return row
    if (post.price_status & LIQUIDATION_CHECKS) != LIQUIDATION_CHECKS:
        row.update(klass="ORACULO", detail=f"price_status={post.price_status:#08b}: nadie puede liquidar ahora")
        return row
    bl = blockers(post, market, st.reserves)
    est = estimate_liquidation(post, st.reserves, market, capital)
    if bl or est is None:
        row.update(klass="BLOQUEADA", detail=";".join(bl) or "colateral_no_liquidable")
        return row
    C, D = st.reserves[est.coll], st.reserves[est.debt]
    hc = await jup.haircut(C, D, est.sell_raw)
    est.haircut_pct = hc
    est.net_usd = est.net_before_swap - (hc if hc is not None else 0.005) * (est.withdraw_usd - est.prot_fee_usd) - tx_cost
    row.update(bonus_bps=est.bonus * 1e4, net_usd=est.net_usd, flash_ok=int(est.flash_ok),
               haircut_pct=None if hc is None else hc * 100,
               detail=f"{C.name}->{D.name} repay ${est.repay_usd:,.0f}" + ("" if hc is not None else " (slippage supuesto 0.5%)"))
    if est.net_usd < min_profit:
        row["klass"] = "NO_RENTABLE"
    elif not est.flash_ok:
        row["klass"] = "NECESITA_CAPITAL"
    else:
        row["klass"] = "REAL"
    return row


async def cmd_audit(args):
    rpc_url, _ = env_urls()
    rpc, tb, st, con = Rpc(rpc_url, args.rps), TxBuilder(need_payer()), State(), db_open(args.db)
    jup = Jup(os.environ.get("JUP_API_KEY"))
    await load_markets_reserves(rpc, st)
    cur = await rpc.slot()
    if args.candidates:
        keys = read_candidates(args.candidates)
        data = await rpc.multiple(keys, (0, OB_SLICE))
        obs = [decode_obligation(pkb(k), d) for k, d in data.items() if d and d[:8] == DISC_OBLIGATION]
        log(f"candidatas leidas: {len(keys)} | obligations validas: {len(obs)}")
    else:
        await load_obligations(rpc, st, args.market)
        obs = []
        for ob in st.obligations.values():
            if ob.stored_margin < -args.min_margin and ob.deposited_sf / SCALE >= args.min_coll:
                obs.append(ob)
        log(f"criterio de snapshot (margen < -{args.min_margin:.0%}, colateral >= ${args.min_coll:,.0f}): "
            f"{len(obs)} 'liquidables'")
    obs.sort(key=lambda o: o.deposited_sf, reverse=True)
    stale = sum(1 for o in obs if o.stale)
    log(f"del snapshot: {stale}/{len(obs)} tienen last_update.stale=1 (valores guardados invalidos por diseno)")
    rows = []
    sem = asyncio.Semaphore(6)

    async def one(ob):
        async with sem:
            try:
                rows.append(await classify(rpc, tb, st, jup, ob, cur, args.capital, args.min_profit, args.tx_cost))
            except Exception as e:  # noqa
                rows.append({"obligation": pks(ob.pk), "market": pks(ob.market), "klass": "ERROR", "detail": repr(e)[:150]})
            if len(rows) % 100 == 0:
                log(f"  {len(rows)}/{len(obs)}")

    await asyncio.gather(*(one(o) for o in obs))
    ts = time.time()
    cols = ["obligation", "market", "market_name", "klass", "stored_stale", "stored_age_h", "stored_margin",
            "fresh_ratio", "deposit_usd", "debt_usd", "bonus_bps", "net_usd", "flash_ok", "haircut_pct", "detail"]
    for r in rows:
        con.execute(f"INSERT OR REPLACE INTO audit({','.join(cols)},ts) VALUES({','.join('?' * len(cols))},?)",
                    [r.get(c) for c in cols] + [ts])
    con.commit()
    out_csv = f"audit_{time.strftime('%Y%m%d_%H%M')}.csv"
    with open(out_csv, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)
    print_audit(rows, stale, len(obs))
    log(f"CSV: {out_csv} | creditos usados: ~{rpc.credits}")


def print_audit(rows: list, stale: int, n: int):
    from collections import Counter, defaultdict
    cnt = Counter(r["klass"] for r in rows)
    print("\n=== AUDITORIA DE CANDIDATAS (precios de ahora, refresh simulado) ===")
    for k in ["REAL", "NECESITA_CAPITAL", "NO_RENTABLE", "BLOQUEADA", "ORACULO", "FANTASMA", "REFRESH_FALLA", "ERROR"]:
        if cnt.get(k):
            print(f"  {k:<17} {cnt[k]:>6}  ({cnt[k] / max(1, len(rows)):.0%})")
    by_m = defaultdict(Counter)
    for r in rows:
        by_m[r.get("market_name") or r["market"][:8]][r["klass"]] += 1
    print("\n  por mercado (top 12):")
    for m, c in sorted(by_m.items(), key=lambda x: -sum(x[1].values()))[:12]:
        print(f"    {m[:28]:<28} " + " ".join(f"{k}={v}" for k, v in c.most_common()))
    reals = sorted([r for r in rows if r["klass"] in ("REAL", "NECESITA_CAPITAL")], key=lambda r: -(r["net_usd"] or 0))
    if reals:
        print("\n  ejecutables hoy (top 10 por neto estimado):")
        for r in reals[:10]:
            print(f"    {r['obligation'][:10]}.. {r['market_name'][:18]:<18} bonus {r['bonus_bps']:.0f}bps "
                  f"neto ${r['net_usd']:,.2f} {'flash' if r['flash_ok'] else 'CAPITAL'} | {r['detail']}")
    print(f"\n  snapshot: {stale}/{n} con stale=1. Suma neta ejecutable ahora: "
          f"${sum(r['net_usd'] or 0 for r in reals):,.2f}\n")


# ----------------------------------------------------------------------------------------------
# Comando: run (censo + vigia)
# ----------------------------------------------------------------------------------------------
class Runner:
    def __init__(self, args):
        self.args = args
        rpc_url, self.ws_url = env_urls()
        self.rpc = Rpc(rpc_url, args.rps)
        self.tb = TxBuilder(need_payer())
        self.st = State()
        self.con = db_open(args.db)
        self.jup = Jup(os.environ.get("JUP_API_KEY"))
        self.txq: asyncio.Queue = asyncio.Queue()
        self.sim_bucket = Bucket(args.max_sims_per_sec)
        self.main_market = pkb(MAIN_MARKET)
        self.markets_filter = [m for m in (args.market or [])]
        self.t0 = time.time()

    # ---------- modelo en memoria
    def recompute(self, keys) -> None:
        st, a = self.st, self.args
        for k in keys:
            ob = st.obligations.get(k)
            m = st.markets.get(ob.market) if ob else None
            if ob is None or m is None or m.price_liq_disabled or (a.skip_main and ob.market == self.main_market) \
                    or (m.perm_authority != ZERO32 and m.perm_ops & PERM_LIQUIDATE) \
                    or any(r in st.bad_reserves for r in ob.reserves()):
                st.warm.discard(k)
                continue
            mh = model_health(ob, st.reserves, m)
            if mh is None:
                continue
            ratio, _, debt = mh
            st.ratio[k], st.debt[k] = ratio, debt
            if debt < a.min_debt:
                st.warm.discard(k)
                continue
            if ratio >= a.warm:
                st.warm.add(k)
            else:
                st.warm.discard(k)
            if ratio >= 1.0 - a.eps and time.monotonic() >= st.cooldown.get(k, 0):
                st.candidates[k] = max(st.candidates.get(k, 0), ratio * math.log10(10 + debt))

    def active_obligations(self):
        if self.args.skip_main:
            return [k for k, o in self.st.obligations.items() if o.market != self.main_market]
        return list(self.st.obligations)

    def reserves_of(self, keys) -> list[bytes]:
        rs = set()
        for k in keys:
            ob = self.st.obligations.get(k)
            if ob and self.st.debt.get(k, self.args.min_debt) >= self.args.min_debt:
                rs.update(ob.reserves())
        return list(rs)

    # ---------- loops
    async def sweep_loop(self):
        while not self.st.stop:
            t = time.monotonic()
            try:
                keys = self.active_obligations()
                await sim_refresh_reserves(self.rpc, self.tb, self.st, self.reserves_of(keys))
                self.recompute(keys)
            except Exception as e:
                log("sweep error:", repr(e)[:200])
            await asyncio.sleep(max(1.0, self.args.sweep_interval - (time.monotonic() - t)))

    async def warm_loop(self):
        while not self.st.stop:
            t = time.monotonic()
            try:
                keys = list(self.st.warm)
                if keys:
                    await sim_refresh_reserves(self.rpc, self.tb, self.st, self.reserves_of(keys))
                    self.recompute(keys)
            except Exception as e:
                log("warm error:", repr(e)[:200])
            await asyncio.sleep(max(0.5, self.args.price_interval - (time.monotonic() - t)))

    async def sync_loop(self):
        """Cambios en obligations (deposits/repays/liquidaciones) cada 60s via changedSinceSlot.
        Si tu RPC no soporta changedSinceSlot, rescan completo como maximo cada 15 min."""
        last, last_full, warned = await self.rpc.slot(), time.monotonic(), False
        while not self.st.stop:
            await asyncio.sleep(60)
            try:
                now = await self.rpc.slot()
                changed = []
                for m in (self.markets_filter or [None]):
                    changed += await self.rpc.program_accounts(ob_filters(m, has_debt=False), (0, OB_SLICE),
                                                               changed_since=last - 150)
                keys = []
                for k, d in changed:
                    ob = decode_obligation(pkb(k), d)
                    if ob.has_debt:
                        self.st.obligations[ob.pk] = ob
                        keys.append(ob.pk)
                    else:
                        self.st.obligations.pop(ob.pk, None)
                        self.st.warm.discard(ob.pk)
                self.recompute(keys)
                last = now
            except Exception as e:
                if not warned:
                    log("sync incremental no disponible, rescan completo cada 15 min:", repr(e)[:160])
                    warned = True
                if time.monotonic() - last_full >= 900:
                    try:
                        await load_obligations(self.rpc, self.st, self.markets_filter or None)
                        last, last_full = await self.rpc.slot(), time.monotonic()
                        self.recompute(self.active_obligations())
                    except Exception as e2:
                        log("rescan error:", repr(e2)[:160])

    async def confirm_loop(self):
        st, a = self.st, self.args
        while not st.stop:
            now = time.monotonic()
            due = [k for k, o in st.open_opps.items() if now - o.last_check >= a.confirm_interval]
            if due:
                k = due[0]
            elif st.candidates:
                k = max(st.candidates, key=st.candidates.get)
                st.candidates.pop(k)
            else:
                await asyncio.sleep(0.2)
                continue
            await self.sim_bucket.take()
            try:
                await self.confirm(k)
            except Exception as e:
                log("confirm error:", repr(e)[:200])

    async def fetch_ob(self, k: bytes) -> Ob | None:
        d = (await self.rpc.multiple([pks(k)], (0, OB_SLICE))).get(pks(k))
        if not d or d[:8] != DISC_OBLIGATION:
            return None
        ob = self.st.obligations[k] = decode_obligation(k, d)
        return ob

    async def confirm(self, k: bytes):
        st, a = self.st, self.args
        ob = st.obligations.get(k)
        # tras una liquidacion las posiciones cambian: releer la cuenta (1 credito)
        if ob is None or st.last_slot - st.recent_liq.get(k, -10 ** 9) < 900:
            ob = await self.fetch_ob(k)
            if ob is None:
                return
        market = st.markets.get(ob.market)
        slot, post, err = await sim_refresh_obligation(self.rpc, self.tb, st, ob)
        if err == "InvalidAccountInput":           # la cuenta cambio desde nuestra ultima lectura
            ob = await self.fetch_ob(k)
            if ob is None:
                return
            slot, post, err = await sim_refresh_obligation(self.rpc, self.tb, st, ob)
        st.last_slot = max(st.last_slot, slot)
        opp = st.open_opps.get(k)
        if opp:
            opp.last_check = time.monotonic()
        est, why = None, None
        if err or post is None:
            why = f"error:{err}"
        elif not (post.bfadv_sf >= post.unhealthy_sf > 0):
            why = "sano"
        elif (post.price_status & LIQUIDATION_CHECKS) != LIQUIDATION_CHECKS:
            why = "oraculo"
        elif blockers(post, market, st.reserves):
            why = "bloqueada"
        else:
            est = estimate_liquidation(post, st.reserves, market, a.capital)
            if est is None:
                why = "colateral_no_liquidable"
            else:
                C, D = st.reserves[est.coll], st.reserves[est.debt]
                hc = await self.jup.haircut(C, D, est.sell_raw)
                est.haircut_pct = hc
                est.net_usd = est.net_before_swap - (hc if hc is not None else 0.005) * \
                    (est.withdraw_usd - est.prot_fee_usd) - a.tx_cost
                if est.net_usd < a.min_profit:
                    why = "no_rentable"
        if why:
            st.cooldown[k] = time.monotonic() + 20
            if opp:
                closed = self.close_opp(k, slot, why)
                if closed:
                    st.recently_closed[k] = (closed, time.monotonic())
            return
        if opp is None:
            kind = "remanente" if slot - st.recent_liq.get(k, -10 ** 9) < 300 else "nueva"
            opp = Opp(k, ob.market, slot, time.time(), kind, est.net_usd, slot, time.monotonic())
            cur = self.con.execute(
                "INSERT INTO opportunities(obligation,market,kind,first_slot,first_ts,last_slot,est_open_usd,"
                "capturable,bonus_bps,repay_usd,flash_ok,haircut_pct,is_main) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)",
                (pks(k), pks(ob.market), kind, slot, opp.first_ts, slot, est.net_usd, 0, est.bonus * 1e4,
                 est.repay_usd, int(est.flash_ok), None if est.haircut_pct is None else est.haircut_pct * 100,
                 int(ob.market == self.main_market)))
            self.con.commit()
            opp.db_id = cur.lastrowid
            st.open_opps[k] = opp
            st.stats["opps"] += 1
        opp.last_slot = slot
        if not opp.capturable and slot - opp.first_slot >= a.L:
            opp.capturable, opp.est_at_L = 1, est.net_usd
            st.stats["capt"] += 1
            self.con.execute("UPDATE opportunities SET capturable=1, est_at_L_usd=? WHERE id=?", (est.net_usd, opp.db_id))
        self.con.execute("UPDATE opportunities SET last_slot=? WHERE id=?", (slot, opp.db_id))
        self.con.commit()

    def close_opp(self, k: bytes, slot: int, reason: str, liquidator: str | None = None):
        opp = self.st.open_opps.pop(k, None)
        if opp and opp.db_id:
            self.con.execute("UPDATE opportunities SET close_slot=?, close_reason=?, liquidator=? WHERE id=?",
                             (slot, reason, liquidator, opp.db_id))
            self.con.commit()
        return opp

    # ---------- censo
    async def ws_loop(self):
        import websockets
        sub = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "logsSubscribe",
                          "params": [{"mentions": [KLEND]}, {"commitment": "confirmed"}]})
        backoff = 1
        while not self.st.stop:
            try:
                async with websockets.connect(self.ws_url, ping_interval=20, ping_timeout=30,
                                              max_size=2 ** 23) as ws:
                    await ws.send(sub)
                    backoff = 1
                    async for raw in ws:
                        self.st.ws_bytes += len(raw)
                        if ATTEMPT_MARK not in raw and "pnl: Liquidator" not in raw:
                            continue
                        msg = json.loads(raw)
                        res = msg.get("params", {}).get("result", {})
                        v, slot = res.get("value", {}), res.get("context", {}).get("slot", 0)
                        self.on_logs(v.get("signature"), slot, v.get("err"), v.get("logs") or [])
            except Exception as e:
                log("websocket caido, reconecto:", repr(e)[:120])
                await asyncio.sleep(backoff)
                backoff = min(60, backoff * 2)

    def on_logs(self, sig: str, slot: int, err, logs: list):
        recs = parse_liq_logs(logs) if not err else []
        self.con.execute("INSERT OR IGNORE INTO attempts VALUES(?,?,?,?,?,?)",
                         (sig, slot, time.time(), int(err is None), None if err is None else json.dumps(err)[:100],
                          len(recs)))
        self.con.commit()
        if err is None and recs:
            self.st.stats["liq_ok"] += len(recs)
            self.txq.put_nowait((sig, slot, recs))
        elif err is not None:
            self.st.stats["liq_fail"] += 1

    async def tx_worker(self):
        while not self.st.stop:
            sig, slot, recs = await self.txq.get()
            try:
                tx = None
                for i in range(6):
                    tx = await self.rpc.call("getTransaction", [sig, {"encoding": "json", "commitment": "confirmed",
                                                                      "maxSupportedTransactionVersion": 0}])
                    if tx:
                        break
                    await asyncio.sleep(1.5)
                if not tx:
                    continue
                ixs = parse_liq_ixs(tx)
                need = [r for ix in ixs for r in (ix["repay_reserve"], ix["withdraw_reserve"]) if pkb(r) not in self.st.reserves]
                if need:
                    for k, d in (await self.rpc.multiple(list(set(need)), (0, RES_SLICE))).items():
                        if d:
                            self.st.reserves[pkb(k)] = decode_reserve(pkb(k), d)
                for idx, (ix, rec) in enumerate(zip(ixs, recs)):
                    Rr, Rw = self.st.reserves.get(pkb(ix["repay_reserve"])), self.st.reserves.get(pkb(ix["withdraw_reserve"]))
                    repay_usd = Rr.usd(rec["repay_raw"]) if Rr else None
                    profit = (Rw.usd(rec["withdraw_raw"]) - repay_usd) if (Rw and Rr) else None
                    obk = pkb(ix["obligation"])
                    opp = self.close_opp(obk, slot, "liquidada_por_otro", ix["liquidator"])
                    if opp is None and obk in self.st.recently_closed:
                        # nuestro chequeo la vio sana DESPUES de que otro la liquidara: re-etiquetar
                        old, t_closed = self.st.recently_closed.pop(obk)
                        if time.monotonic() - t_closed < 120 and slot >= old.first_slot and old.db_id:
                            self.con.execute("UPDATE opportunities SET close_slot=?, close_reason=?, liquidator=? "
                                             "WHERE id=?", (slot, "liquidada_por_otro", ix["liquidator"], old.db_id))
                            opp = old
                    seen, lead = (1, slot - opp.first_slot) if opp else (0, None)
                    self.st.recent_liq[obk] = slot
                    self.st.candidates[obk] = 10.0            # medir el remanente (close factor 10%)
                    self.con.execute(
                        "INSERT OR IGNORE INTO liquidations VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                        (sig, idx, slot, time.time(), rec["reason"], rec["bonus_bps"], rec["ltv"], rec["liq_ltv"],
                         ix["liquidator"], ix["fee_payer"], ix["obligation"], ix["market"], ix["repay_mint"],
                         ix["withdraw_mint"], rec["repay_raw"], rec["withdraw_raw"], rec["fee_raw"], repay_usd,
                         profit, ix["fee"], ix["tip"], ix["cpi"], ix["outer_program"], seen, lead))
                self.con.commit()
            except Exception as e:
                log("tx_worker error:", repr(e)[:200])

    async def status_loop(self):
        while not self.st.stop:
            await asyncio.sleep(300)
            s, h = self.st.stats, (time.time() - self.t0) / 3600
            ws_credits = self.st.ws_bytes / 1e6 * 20
            total = self.rpc.credits + ws_credits
            log(f"[{h:.1f}h] liq ok={s['liq_ok']} fallidas={s['liq_fail']} | opps={s['opps']} capturables={s['capt']} "
                f"abiertas={len(self.st.open_opps)} | warm={len(self.st.warm)} cand={len(self.st.candidates)} "
                f"| sims={s['sims']} | creditos ~{total:,.0f} (proy/dia ~{total / max(h, 1e-3) * 24:,.0f})")
            meta_set(self.con, "run_progress", {"hours": h, "credits": total, **s})

    async def main(self):
        a = self.args
        log(f"run: {a.hours}h | L={a.L} slots | min_profit=${a.min_profit} | capital=${a.capital} | db={a.db}")
        await load_markets_reserves(self.rpc, self.st)
        await load_obligations(self.rpc, self.st, self.markets_filter or None)
        meta_set(self.con, "run_start", {"ts": time.time(), "hours": a.hours, "L": a.L, "min_profit": a.min_profit,
                                         "skip_main": a.skip_main, "markets": self.markets_filter})
        keys = self.active_obligations()
        await sim_refresh_reserves(self.rpc, self.tb, self.st, self.reserves_of(keys))
        self.recompute(keys)
        log(f"warm={len(self.st.warm)} candidatas={len(self.st.candidates)} "
            f"reserves_no_refrescables={len(self.st.bad_reserves)}")
        tasks = [asyncio.create_task(c) for c in (self.ws_loop(), self.tx_worker(), self.sweep_loop(),
                                                   self.warm_loop(), self.sync_loop(), self.confirm_loop(),
                                                   self.status_loop())]
        try:
            await asyncio.sleep(a.hours * 3600)
        finally:
            self.st.stop = True
            for k in list(self.st.open_opps):
                self.close_opp(k, self.st.last_slot, "fin_del_test")
            meta_set(self.con, "run_end", {"ts": time.time(), "credits": self.rpc.credits + self.st.ws_bytes / 1e6 * 20})
            for t in tasks:
                t.cancel()
            log("fin. Corre: python3 centinela_test7d.py report --db", a.db)


async def cmd_run(args):
    await Runner(args).main()


# ----------------------------------------------------------------------------------------------
# Comando: report (metrica binaria)
# ----------------------------------------------------------------------------------------------
def pct(xs: list, q: float):
    xs = sorted(x for x in xs if x is not None)
    if not xs:
        return None
    return xs[min(len(xs) - 1, int(q * (len(xs) - 1) + 0.5))]


def compute_report(con, week_profit: float = 120.0, week_events: int = 5, week_valid: int = 100) -> dict:
    start = meta_get(con, "run_start", {})
    end = meta_get(con, "run_end", {})
    t0 = start.get("ts") or (con.execute("SELECT MIN(ts) FROM attempts").fetchone()[0] or time.time())
    t1 = end.get("ts") or (con.execute("SELECT MAX(ts) FROM attempts").fetchone()[0] or time.time())
    hours = max((t1 - t0) / 3600, 1e-6)
    k = hours / 168.0
    liq = con.execute("SELECT reason,bonus_bps,ltv_pct,liq_ltv_pct,liquidator,market,repay_usd,profit_usd,"
                      "tip_lamports,seen_by_us,lead_slots,cpi FROM liquidations").fetchall()
    n_liq = len(liq)
    n_fail = con.execute("SELECT COUNT(*) FROM attempts WHERE ok=0").fetchone()[0]
    from collections import Counter
    by_liq = Counter(r[4] for r in liq)
    prof_by = Counter()
    for r in liq:
        prof_by[r[4]] += r[7] or 0
    tot_profit = sum(r[7] or 0 for r in liq)
    opps = con.execute("SELECT kind,first_slot,close_slot,close_reason,est_open_usd,est_at_L_usd,capturable,"
                       "flash_ok,is_main FROM opportunities").fetchall()
    capt = [o for o in opps if o[6]]
    capt_usd = sum(o[5] or 0 for o in capt)
    lifetimes = [o[2] - o[1] for o in opps if o[3] == "liquidada_por_otro" and o[2] is not None]
    valid = n_liq >= week_valid * k
    go = len(capt) >= math.ceil(week_events * k) and capt_usd >= week_profit * k
    verdict = "SEGUI" if (valid and go) else ("EXTENDE 7 DIAS" if not valid else "CORTA")
    if go and not valid:
        verdict = "SEGUI"          # si capturaste suficiente, poco flujo no invalida el positivo
    return {
        "hours": hours, "liquidations": n_liq, "failed_attempts": n_fail,
        "unique_liquidators": len(by_liq), "top1_share_count": (by_liq.most_common(1)[0][1] / n_liq) if n_liq else None,
        "top3_share_profit": (sum(v for _, v in prof_by.most_common(3)) / tot_profit) if tot_profit > 0 else None,
        "liquidator_profit_usd": tot_profit, "reasons": dict(Counter(r[0] for r in liq)),
        "bonus_bps_p10_p50_p90": [pct([r[1] for r in liq], q) for q in (0.1, 0.5, 0.9)],
        "ltv_excess_pp_p50": pct([(r[2] - r[3]) for r in liq if r[2] is not None and r[3] is not None], 0.5),
        "main_market_share": (sum(1 for r in liq if r[5] == MAIN_MARKET) / n_liq) if n_liq else None,
        "seen_by_us_share": (sum(1 for r in liq if r[9]) / n_liq) if n_liq else None,
        "lead_slots_p50": pct([r[10] for r in liq if r[10] is not None], 0.5),
        "opportunities": len(opps), "opp_lifetime_slots_p50": pct(lifetimes, 0.5),
        "capturable_events": len(capt), "capturable_usd": capt_usd,
        "capturable_non_main_usd": sum(o[5] or 0 for o in capt if not o[8]),
        "capturable_need_capital": sum(1 for o in capt if not o[7]),
        "thresholds": {"events": math.ceil(week_events * k), "usd": week_profit * k, "valid_liqs": week_valid * k},
        "valid": valid, "verdict": verdict,
    }


def cmd_report(args):
    con = db_open(args.db)
    r = compute_report(con, args.week_profit, args.week_events, args.week_valid)
    f = lambda x, s="{:,.2f}": "-" if x is None else s.format(x)  # noqa
    print(f"\n=== REPORTE ({r['hours']:.1f} h) ===")
    print(f"Censo: {r['liquidations']} liquidaciones exitosas, {r['failed_attempts']} intentos fallidos on-chain, "
          f"{r['unique_liquidators']} liquidadores distintos")
    print(f"  ganancia bruta total de TODOS los liquidadores: ${f(r['liquidator_profit_usd'])}")
    print(f"  top-1 por cantidad: {f(r['top1_share_count'], '{:.0%}')} | top-3 por ganancia: {f(r['top3_share_profit'], '{:.0%}')}")
    print(f"  bonus ejecutado p10/p50/p90 (bps): {r['bonus_bps_p10_p50_p90']} | LTV sobre umbral p50: "
          f"{f(r['ltv_excess_pp_p50'], '{:.1f}')} pp | motivos: {r['reasons']}")
    print(f"  mercado principal: {f(r['main_market_share'], '{:.0%}')} de las liquidaciones")
    print(f"Tu vigia: vio antes {f(r['seen_by_us_share'], '{:.0%}')} de las liquidaciones "
          f"(ventaja p50: {f(r['lead_slots_p50'], '{:.0f}')} slots)")
    print(f"  oportunidades detectadas: {r['opportunities']} | vida p50 hasta que otro la toma: "
          f"{f(r['opp_lifetime_slots_p50'], '{:.0f}')} slots")
    t = r["thresholds"]
    print("\nMETRICA BINARIA: oportunidades que siguieron abiertas >= L slots y dejaban >= min_profit")
    print(f"  capturables: {r['capturable_events']} (umbral {t['events']}) | valor: ${f(r['capturable_usd'])} "
          f"(umbral ${t['usd']:,.0f}) | fuera del mercado principal: ${f(r['capturable_non_main_usd'])} | "
          f"requieren capital propio: {r['capturable_need_capital']}")
    print(f"  validez: {r['liquidations']} liquidaciones en el periodo (minimo {t['valid_liqs']:.0f})")
    print(f"\nVEREDICTO: {r['verdict']}\n")
    if args.json:
        print(json.dumps(r, indent=2, default=str))


# ----------------------------------------------------------------------------------------------
def main():
    p = argparse.ArgumentParser(description="Centinela: test de 7 dias para liquidaciones en Kamino")
    p.add_argument("--rps", type=float, default=20, help="tope de requests/s al RPC (Developer: 50)")
    p.add_argument("--db", default="centinela_test.db")
    sub = p.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("selftest")
    s.add_argument("--n", type=int, default=40, help="obligations a comparar modelo vs on-chain")

    s = sub.add_parser("audit")
    s.add_argument("--candidates", help="archivo con pubkeys de obligations (txt/csv). Sin esto, escanea.")
    s.add_argument("--market", action="append", help="limitar el escaneo a este mercado (repetible)")
    s.add_argument("--min-margin", type=float, default=0.01, help="criterio de snapshot: margen < -X")
    s.add_argument("--min-coll", type=float, default=0.0, help="colateral minimo (USD, valor guardado)")
    s.add_argument("--capital", type=float, default=500.0)
    s.add_argument("--min-profit", type=float, default=2.0)
    s.add_argument("--tx-cost", type=float, default=0.05, help="USD por liquidacion (fee+prioridad)")

    s = sub.add_parser("run")
    s.add_argument("--hours", type=float, default=168)
    s.add_argument("--market", action="append", help="solo estos mercados (repetible)")
    s.add_argument("--skip-main", action="store_true", help="excluir el mercado principal (foco cola larga)")
    s.add_argument("--L", type=int, default=10, help="slots que debe seguir abierta para contar como capturable")
    s.add_argument("--min-profit", type=float, default=2.0)
    s.add_argument("--min-debt", type=float, default=50.0, help="ignorar obligations con deuda menor (USD)")
    s.add_argument("--capital", type=float, default=500.0)
    s.add_argument("--tx-cost", type=float, default=0.05)
    s.add_argument("--warm", type=float, default=0.97, help="ratio bfadv/ubv para vigilar de cerca")
    s.add_argument("--eps", type=float, default=0.002, help="margen del modelo para pedir confirmacion exacta")
    s.add_argument("--price-interval", type=float, default=8.0, help="s entre refresh de precios (warm)")
    s.add_argument("--sweep-interval", type=float, default=60.0, help="s entre barridos completos")
    s.add_argument("--confirm-interval", type=float, default=1.5, help="s entre chequeos de una opp abierta")
    s.add_argument("--max-sims-per-sec", type=float, default=3.0)

    s = sub.add_parser("report")
    s.add_argument("--week-profit", type=float, default=120.0, help="USD capturables por 7 dias para SEGUIR")
    s.add_argument("--week-events", type=int, default=5, help="eventos capturables por 7 dias para SEGUIR")
    s.add_argument("--week-valid", type=int, default=100, help="liquidaciones minimas para que la semana cuente")
    s.add_argument("--json", action="store_true")

    args = p.parse_args()
    if args.cmd == "report":
        cmd_report(args)
    else:
        fn = {"selftest": cmd_selftest, "audit": cmd_audit, "run": cmd_run}[args.cmd]
        try:
            asyncio.run(fn(args))
        except KeyboardInterrupt:
            log("interrumpido")


if __name__ == "__main__":
    main()
