/-
  Benchmark.Grindset.Tests — demonstration proofs closed by a single `grind`.

  These proofs are written from scratch against `Specs.lean` + `Contract.lean`.
  They deliberately do NOT import any `Proofs.lean` from under
  `Benchmark/Cases/` — the held-out ground truth is never consulted.

  Each demo theorem has the same shape as the sorry-stubs in
  `Benchmark/Generated/.../Tasks/*.lean`, and is discharged by a single
  invocation of `grind` (plus, where needed, an `unfold` of the spec
  predicate).
-/

import Benchmark.Grindset.Core
import Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.Specs
import Benchmark.Cases.Lido.VaulthubLocked.Specs

namespace Benchmark.Grindset.Tests

open Verity
open Verity.EVM.Uint256

/-! ## SideEntrance.deposit: slot-write spec -/

/--
Demo #1: `deposit` writes `add oldPoolBalance amount` to `poolBalance`.
Closed by a single `grind` call once we unfold the spec predicate and
the contract function.
-/
theorem demo_deposit_sets_pool_balance
    (amount : Verity.Core.Uint256)
    (s : ContractState) :
    let s' :=
      ((Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.deposit amount).run s).snd
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_pool_balance_spec
      amount s s' := by
  simp only [grind_norm,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_pool_balance_spec,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.deposit,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.poolBalance,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.totalCredits,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.creditOf]
  grind

/--
Demo #2: `deposit` credits the caller's mapping slot by `amount`.
This is the "mapping + sender" variant; we rely on
`storageMap_setMapping_sender_eq` (from `Core.lean`) plus `grind_norm` to
collapse the monadic do-block.
-/
theorem demo_deposit_sets_sender_credit
    (amount : Verity.Core.Uint256)
    (s : ContractState) :
    let s' :=
      ((Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.deposit amount).run s).snd
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_sender_credit_spec
      amount s s' := by
  simp only [grind_norm,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.deposit_sets_sender_credit_spec,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.deposit,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.poolBalance,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.totalCredits,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.creditOf]
  grind

/--
Demo #3: `flashLoanViaDeposit` preserves pool balance. This is a branchy
case because the function body starts with a `require (amount <= oldPoolBalance)`.
The precondition `hBorrow` discharges the branch; the remaining reasoning is
the same slot-write logic as `deposit`.
-/
theorem demo_flashLoanViaDeposit_preserves_pool_balance
    (amount : Verity.Core.Uint256)
    (s : ContractState)
    (hBorrow : amount <= s.storage 0) :
    let s' :=
      ((Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.flashLoanViaDeposit
          amount).run s).snd
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.flashLoanViaDeposit_preserves_pool_balance_spec
      amount s s' := by
  simp only [grind_norm,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.flashLoanViaDeposit_preserves_pool_balance_spec,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.flashLoanViaDeposit,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.poolBalance,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.totalCredits,
    Benchmark.Cases.DamnVulnerableDeFi.SideEntrance.SideEntrance.creditOf, hBorrow]
  grind

end Benchmark.Grindset.Tests
