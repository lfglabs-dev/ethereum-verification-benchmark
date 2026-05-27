import Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.DamnVulnerableDeFi.SideEntrance

open Verity
open Verity.EVM.Uint256

/--
Executing the summarized flash-loan-plus-deposit path leaves tracked pool ETH
unchanged.
-/
theorem flashLoanViaDeposit_preserves_pool_balance
    (amount : Uint256) (s : ContractState)
    (hBorrow : amount <= s.storage 0) :
    let s' := ((SideEntrance.flashLoanViaDeposit amount).run s).snd
    flashLoanViaDeposit_preserves_pool_balance_spec amount s s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold flashLoanViaDeposit_preserves_pool_balance_spec
  grind [SideEntrance.flashLoanViaDeposit, SideEntrance.poolBalance, SideEntrance.totalCredits, SideEntrance.creditOf]

end Benchmark.Cases.DamnVulnerableDeFi.SideEntrance
