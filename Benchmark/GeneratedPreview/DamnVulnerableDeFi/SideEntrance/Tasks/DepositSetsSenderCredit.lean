import Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.DamnVulnerableDeFi.SideEntrance

open Verity
open Verity.EVM.Uint256

/--
Executing `deposit` increases the caller's credited balance by `amount`.
-/
theorem deposit_sets_sender_credit
    (amount : Uint256) (s : ContractState) :
    let s' := ((SideEntrance.deposit amount).run s).snd
    deposit_sets_sender_credit_spec amount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold deposit_sets_sender_credit_spec
  grind [SideEntrance.deposit, SideEntrance.poolBalance, SideEntrance.totalCredits, SideEntrance.creditOf]

end Benchmark.Cases.DamnVulnerableDeFi.SideEntrance
