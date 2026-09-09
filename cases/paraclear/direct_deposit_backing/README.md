# Paraclear direct-deposit backing

This case proves one local preservation property for the Paraclear Cairo clearing
contract:

> A successful modeled `deposit` or `deposit_on_behalf_of` call cannot reduce the
> deposited token's backing slack.

For token `t`, backing slack is raw ERC20 custody normalized to Paraclear's eight
decimals minus the sum of positive posted internal balances. The result covers signed
recipient balances, Cairo's decimal-flooring behavior, exact ERC20 receipt checks,
account creation, guards, and unrelated-balance framing.

## Source provenance

The selected Cairo source was supplied privately for this engagement. It is not copied
into this public benchmark and no public upstream commit or deployed class hash was
provided. The reviewed local extraction was dated 2026-09-07. The canonical project
paths below include the source repository's `src/` prefix; the supplied extraction
root contained the same hash-matching files at `paraclear/paraclear.cairo` and
`token/token.cairo`. Relevant file hashes:

- `src/paraclear/paraclear.cairo`:
  `279c4aa39ae6ecdeacadc63d2003a71639a458821edecceef0b278ef5fed7e2e`
- `src/token/token.cairo`:
  `bdaee8fd6c63f259683688629ad57e76be3df86da892936183a11256803b9959`

Source paths and reviewed ranges:

| Behavior | Cairo source |
|---|---|
| Public `deposit` and `deposit_on_behalf_of` | `src/paraclear/paraclear.cairo:2477-2513` |
| Per-token pause and no-manager branch | `src/paraclear/paraclear.cairo:3259-3272` |
| `upsert_asset_balance` observable amount update | `src/token/token.cairo:294-333` |
| Decimal conversions | `src/token/token.cairo:412-440` |
| Support and registry checks | `src/token/token.cairo:442-487` |
| Internal `_deposit` | `src/token/token.cairo:576-620` |

## Verification boundary

This is a pure Lean, source-aligned state machine packaged as a benchmark task. Verity's
current EDSL targets Solidity/EVM contracts and does not translate Cairo. The proof is
therefore not a Cairo/Sierra/CASM/deployed-class correspondence proof.

The real-code interpretation assumes stable ERC20 decimal metadata and treats Assets
Manager, registry, and ERC20 dispatcher calls as atomic observations. Callback traces
are excluded. Bridge deposits, withdrawals, settlement, fees, liquidations, pending
transfers, socialized-loss application, later rebases, and arbitrary later ERC20
behavior require separate cases.

## Verify

```bash
lake build Benchmark.Cases.Paraclear.DirectDepositBacking.Contract
lake build Benchmark.Cases.Paraclear.DirectDepositBacking.Specs
lake build Benchmark.Cases.Paraclear.DirectDepositBacking.Proofs
lake build Benchmark.Cases.Paraclear.DirectDepositBacking.Compile
python3 scripts/validate_manifests.py
python3 scripts/check_reference_solutions.py
```

The generated task file intentionally ends in `exact ?_`; it is the agent-editable
benchmark prompt. The complete checked proof lives in the reference `Proofs.lean`.

Public protocol context is available in Paradex's
[security documentation](https://docs.paradex.trade/chain/security/audit-pentests) and
[wallet overview](https://docs.paradex.trade/docs/accounts/wallet-overview). StarkWare's
[STRK20 write-up](https://starkware.co/blog/strk20-formal-verification/) is the precedent
for using a separately checked Lean state-machine development around Cairo protocol
logic while keeping implementation correspondence explicit.
