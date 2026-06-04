# Evaluated Surface

This page is generated from the benchmark manifests by `scripts/generate_metadata.py`.
The canonical machine inventory is `benchmark-inventory.json`, generated
from `cases/*/*/case.yaml`, `cases/*/*/tasks/*.yaml`, `backlog/*/*/case.yaml`,
and `backlog/*/*/tasks/*.yaml`.

## Active Suite

The active suite currently contains 25 cases and 134 task manifests. Of those, 133 tasks are runnable proof tasks with hidden reference proofs; the remaining 1 active task is present in manifests but not runnable.

| Case | Runnable Tasks | Case Proof Status |
|------|---------------:|-------------------|
| `alchemix/earmark_conservation` | 5 | `complete` |
| `balancer/reclamm_swap_rounding` | 1 | `complete` |
| `cork/pool_solvency` | 1 | `partial` |
| `damn_vulnerable_defi/side_entrance` | 5 | `partial` |
| `ethereum/deposit_contract_minimal` | 5 | `partial` |
| `forgeyields/global_solvency` | 7 | `complete` |
| `ipor/plasma_vault_redeem_split` | 2 | `complete` |
| `kleros/sortition_trees` | 6 | `partial` |
| `lagoon/guardrails` | 3 | `complete` |
| `lido/vaulthub_locked` | 5 | `partial` |
| `nexus_mutual/ramm_price_band` | 4 | `partial` |
| `onedelta/caller_address_integrity` | 10 | `complete` |
| `paladin_votes/stream_recovery_claim_usdc` | 26 | `complete` |
| `piku/fund_conservation` | 4 | `complete` |
| `polaris/bonding_curve` | 0 | `complete` |
| `polygon/agglayer_bridge` | 2 | `complete` |
| `reserve/auction_price_band` | 4 | `complete` |
| `rootstock/flyover_quote_lifecycle` | 3 | `complete` |
| `safe/owner_manager_reach` | 15 | `complete` |
| `term_finance/term_auction_clearing` | 0 | `proof` |
| `termmax/order_v2_buy_xt_single_segment` | 1 | `complete` |
| `usual/dao_collateral` | 5 | `complete` |
| `wildcat/borrow_liquidity_safety` | 1 | `complete` |
| `zama/erc7984_confidential_token` | 11 | `partial` |
| `zodiac/roles_decoder_faithfulness` | 3 | `complete` |

## Backlog

Backlog cases are not part of the default active suite, but the runnable backlog tasks are still checked for hidden reference proofs. The backlog currently has 8 runnable tasks across `openzeppelin/erc4626_virtual_offset_deposit` and `uniswap_v2/pair_fee_adjusted_swap`.
Blocked backlog cases with no runnable tasks: `usual/placeholder`.

## Non-Evaluated Preview Files

`Benchmark/GeneratedPreview/` is a staging area produced by
`scripts/generate_task_skeletons.py --preview`. Files there are not evaluated
unless a task manifest points to a corresponding `Benchmark/Generated/...`
editable proof file. Backlog manifests are likewise outside the default active
suite until promoted into `cases/`.

## Status Semantics

`proof_status: complete` at case level means the case family is fully covered
by runnable tasks. `proof_status: partial` means the broader family is not yet
fully covered; it does not mean the listed runnable tasks lack hidden reference
proofs.

## Known Coverage Gaps

The suite is strongest on accounting, state preservation, storage effects,
linked-list ownership structures, and solvency invariants. It is thinner on
reentrancy beyond modeled guards, oracle manipulation, governance and timelock
properties, temporal or liveness properties, cross-contract compositional
reasoning, cryptographic assumptions, and adversarial EVM-level behavior.
