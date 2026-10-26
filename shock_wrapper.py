#!/usr/bin/env python3
"""Shock per-obligation: shockea solo reserves del lado colateral."""
import asyncio, argparse, base64, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent / "centinela_risk"))
import centinela_test7d as ct


async def run(args):
    rpc_url, _ = ct.env_urls()
    rpc = ct.Rpc(rpc_url, 10.0)
    await rpc.slot()
    st = ct.State()
    await ct.load_markets_reserves(rpc, st)

    res = await rpc.call("getProgramAccountsV2", [ct.KLEND, {
        "encoding": "base64",
        "filters": ct.ob_filters(ct.MAIN_MARKET),
        "dataSlice": {"offset": 0, "length": ct.OB_SLICE},
        "limit": args.limit,
    }])
    obs = []
    for a in res.get("accounts", []):
        try:
            ob = ct.decode_obligation(ct.pkb(a["pubkey"]),
                                       base64.b64decode(a["account"]["data"][0]))
            obs.append(ob)
        except Exception:
            continue
    print(f"Obligations cargadas: {len(obs)}")

    def health_pre(ob):
        try:
            mh = ct.model_health(ob, st.reserves, st.markets[ob.market])
            return float(mh[0]) if mh else None
        except Exception:
            return None

    print("Calculando PRE...")
    pre = [(ob, health_pre(ob)) for ob in obs]
    pre = [(ob, h) for ob, h in pre if h is not None]
    print(f"Con health válido: {len(pre)}")

    factor_num = 100 + int(args.shock)
    print(f"Shock {args.shock}% per-obligation (solo colateral)...")

    results = []
    for ob, h_pre in pre:
        # Shock solo a las deposit reserves de ESTA obligación
        saved = {}
        for rk, _, _ in ob.deposits:
            if rk in st.reserves:
                saved[rk] = st.reserves[rk].price_sf
                st.reserves[rk].price_sf = st.reserves[rk].price_sf * factor_num // 100
        try:
            mh = ct.model_health(ob, st.reserves, st.markets[ob.market])
            h_post = float(mh[0]) if mh else None
        except Exception:
            h_post = None
        finally:
            for rk, orig in saved.items():
                st.reserves[rk].price_sf = orig
        if h_post is not None:
            results.append((ct.pks(ob.pk), h_pre, h_post))

    liq_pre = sum(1 for _, hp, _ in results if hp >= 1.0)
    liq_post = sum(1 for _, _, hq in results if hq >= 1.0)
    crossed = [(pk, hp, hq) for pk, hp, hq in results if hp < 1.0 and hq >= 1.0]

    out = {
        "slot": await rpc.slot(),
        "shock_pct": args.shock,
        "n_obligations": len(results),
        "liquidable_pre": liq_pre,
        "liquidable_post": liq_post,
        "crossed_count": len(crossed),
        "top_crossed": [{"pk": p, "h_pre": round(hp, 6), "h_post": round(hq, 6)}
                        for p, hp, hq in sorted(crossed, key=lambda x: x[2])[:50]],
    }
    print(json.dumps(out, indent=2))
    Path(args.out).write_text(json.dumps(out, indent=2))
    print(f"\nGuardado en {args.out}")


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--shock", type=float, default=-40.0)
    p.add_argument("--limit", type=int, default=10000)
    p.add_argument("--out", default="/tmp/shock_perob.json")
    asyncio.run(run(p.parse_args()))
