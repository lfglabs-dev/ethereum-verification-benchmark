import Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.DamnVulnerableDeFi.SideEntrance

open Verity
open Verity.EVM.Uint256

/--
Executing the summarized flash-loan-plus-deposit path mints caller credit
equal to the borrowed amount.
-/
theorem flashLoanViaDeposit_sets_sender_credit
    (amount : Uint256) (s : ContractState)
    (hBorrow : amount <= s.storage 0) :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    flashLoanViaDeposit_sets_sender_credit_spec amount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold flashLoanViaDeposit_sets_sender_credit_spec
  grind [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits, SideEntrance.creditOf]

end Benchmark.Cases.DamnVulnerableDeFi.SideEntrance
