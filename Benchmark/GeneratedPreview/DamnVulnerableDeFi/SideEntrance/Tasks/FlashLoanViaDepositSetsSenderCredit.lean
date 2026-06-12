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
  try simp only [grind_norm] at *
  try unfold flashLoanViaDeposit_sets_sender_credit_spec
  try unfold SideEntrance.poolBalance
  try unfold SideEntrance.totalCredits
  try unfold SideEntrance.creditOf
  try unfold SideEntrance.deposit
  try unfold SideEntrance.flashLoanViaDeposit
  try unfold SideEntrance.withdraw
  try unfold deposit_sets_pool_balance_spec
  try unfold deposit_sets_sender_credit_spec
  try unfold flashLoanViaDeposit_preserves_pool_balance_spec
  try unfold flashLoanViaDeposit_sets_sender_credit_spec
  try unfold exploit_trace_drains_pool_spec
  simp [grind_norm, SideEntrance.poolBalance, SideEntrance.totalCredits, SideEntrance.creditOf, SideEntrance.deposit, SideEntrance.flashLoanViaDeposit, SideEntrance.withdraw, deposit_sets_pool_balance_spec, deposit_sets_sender_credit_spec, flashLoanViaDeposit_preserves_pool_balance_spec, flashLoanViaDeposit_sets_sender_credit_spec, exploit_trace_drains_pool_spec, *]
  all_goals try (split_ifs <;> simp_all [grind_norm])
  all_goals try (repeat' (split <;> simp_all [grind_norm]))
  all_goals try omega

end Benchmark.Cases.DamnVulnerableDeFi.SideEntrance
