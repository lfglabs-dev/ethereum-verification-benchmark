# Mistral Medium + Leanstral Hybrid Failure Analysis, 2026-07-09

Artifacts analyzed:

- Suite: `/workspaces/lean-farm/verity-benchmark/results/runs/20260709T100123-default-fair-suite-active`
- Local run root: `/workspaces/lean-farm/verity-benchmark/results/local-runs/20260708T235831Z-mistral-medium-35-driver-labs-leanstral-15-prover-hybrid-full`

The authoritative suite `run.json` contains 200 target outcomes:

- 54 `GENUINE_FAIL`
- 146 `INFRA_INVALID`
- 0 verifier-passing targets

## Top Failure Modes

Counts below are over the 54 `GENUINE_FAIL` targets.

1. One proof attempt was insufficient: 42 targets ended as `max_attempts_exceeded` after one failed `check_proof`/`try_tactics`. In 49 targets the last tool call was a failed `check_proof`, so the model never got to use the structured hint returned by Lean. Examples: `ethereum/deposit_contract_minimal/deposit_count`, `paladin_votes/stream_recovery_claim_usdc/claim_marks_user`, `uniswap_v2/pair_fee_adjusted_swap/swap_sets_reserve1`.
2. Branch splits or leftover `match`/`if` structure: 33 targets had remaining branch/match structure or branch-specific goals. Examples: `ethereum/deposit_contract_minimal/deposit_count`, `damn_vulnerable_defi/side_entrance/exploit_trace_drains_pool`, `paladin_votes/stream_recovery_claim_usdc/both_claim_updates_total_allocated`.
3. Unsolved goals with poor goal extraction: 26 targets ended in `lean_unsolved_goals`, but the compact diagnostic often dropped the actual target or hypotheses, making the retry hint less actionable. Example: `ethereum/deposit_contract_minimal/deposit_count` preserved branch context but not a useful target in the attempt summary.
4. Local file check passed but verifier module build failed: 11 genuine failures had harness status `lean_passed`, then verifier failed with `Benchmark/Grindset.lean:1:0: import Verity.Proofs.Stdlib.Automation failed, environment already contains 'Verity.getStorage.eq_1' from Benchmark.Grindset.Monad`. Examples: `ethereum/deposit_contract_minimal/chain_start_threshold`, `damn_vulnerable_defi/side_entrance/deposit_sets_sender_credit`, `paladin_votes/stream_recovery_claim_usdc/double_claim_rejected`.
5. Bad proof-shape output: 6 targets failed on bad `unfold` strategy, 4 on unknown names, 3 on Lean timeout, and 2 on forbidden placeholders in submitted proof attempts. Examples: `paladin_votes/stream_recovery_claim_usdc/both_no_overclaim`, `lagoon/guardrails/positive_variation_bounded`, `pareto/redemption_backing/deposit_funds_preserves_closed_epoch_reserve_guard`.
6. Hybrid prover was unused: all 54 genuine failures had zero `draft_proof` calls, despite `DEFAULT_HARNESS_PROVER_MODE=draft_proof`. The driver mostly used `show_task`, `read_file`, `show_goal`, then one `check_proof`.

## Implemented Improvements

- `harness/runners/lean_tools.py`: after a successful direct `lake env lean <editable-file>` check, run `lake build <target-module>` before reporting `lean_passed`. This catches dependency/module-build failures before the final verifier.
- `harness/lean_check.py`: compact Lean output now retains the full error block, so unsolved-goal targets and local hypotheses are less likely to be truncated out of tool results.
- `harness/lean_check.py`: goal extraction now stops when the next Lean error begins immediately after a target line, preventing a later error from being folded into the current goal.
- `harness/agents/default.json`: default fair tool-loop attempts increased from 1 to 2. This gives the model one diagnostic-guided retry without adding task-specific hints or reference-proof leakage.
- `tests/test_lean_diagnostics_and_checks.py`: added regression tests for module-build confirmation and full unsolved-goal diagnostic preservation.

## Expected Impact

Expected rerun effect for Mistral Medium + Leanstral:

- The 11 local-pass/verifier-fail cases should no longer be reported as local `lean_passed`; the model will see the module-build failure during the tool loop.
- The 42 one-attempt failures should get one additional chance to respond to Lean diagnostics. This is most likely to help branch-split and simple missing-hypothesis cases, especially where the first attempt already reduced the goal.
- Better diagnostics should improve second attempts on `lean_unsolved_goals` by preserving the remaining target and hypotheses.
- The changes are generic harness behavior. They do not special-case task names, hidden solutions, or reference proofs.

## Blockers And Residual Risks

- The hybrid driver did not call `draft_proof` in this run. Prompting around when to delegate to the prover may need a separate follow-up after this safer retry/checking fix.
- A second proof attempt increases benchmark budget and runtime, but it is a transparent default-budget change and remains generic.
- Some failures are likely real hard proof obligations or require better Verity arithmetic guidance; the implemented changes should not be expected to solve all 54 genuine failures.
