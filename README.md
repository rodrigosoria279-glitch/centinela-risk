# Centinela Risk Engine

An independent, high-precision Python engine for calculating liquidation risk on Kamino Finance (Solana).

## What it does
- Reads on-chain account data directly from the Solana blockchain.
- Reproduces Kamino's `refresh_obligation` math with a maximum error of `1.34e-14` compared to the official Rust implementation.
- Simulates arbitrary collateral price shocks (e.g., SOL -20%, -40%, -60%) to identify positions crossing liquidation thresholds.

## Why it's unique
Most tools rely on Kamino's SDK or approximate the math. This engine reconstructs the calculation from raw binary accounts, providing verifiable precision for risk assessment and stress testing.

## Limitations
- Currently supports Kamino Main Market only.
- Requires a Solana RPC endpoint (Helius recommended).
- For informational purposes only. Not financial advice.

## Usage
*(Instructions coming soon)*
