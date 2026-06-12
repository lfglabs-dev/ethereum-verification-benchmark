import Benchmark.Cases.Wildcat.BorrowLiquiditySafety.Slot0Proof
import Benchmark.Grindset

namespace Benchmark.Cases.Wildcat.BorrowLiquiditySafety

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

private theorem u256_nat_pos {x : Uint256} (h : x > 0) : 0 < (x : Nat) := by
  simpa [Verity.Core.Uint256.lt_def] using h

private theorem totalAssets_after_positive_borrow_ge_required
    (amount totalAssets required : Uint256)
    (hPositive : amount > 0)
    (hAmount : amount <= satSub totalAssets required) :
    totalAssets - amount >= required := by
  by_cases hAvail : totalAssets > required
  · have hReqLeAssets : required <= totalAssets := by
      simp [Verity.Core.Uint256.le_def, Verity.Core.Uint256.lt_def] at hAvail ⊢
      omega
    have hAmount' : amount <= totalAssets - required := by
      simpa [satSub, hAvail] using hAmount
    have hSubReq : ((totalAssets - required : Uint256) : Nat) = (totalAssets : Nat) - (required : Nat) := by
      exact sub_eq_of_le (by simpa [Verity.Core.Uint256.le_def] using hReqLeAssets)
    have hAmountLeAssets : amount <= totalAssets := by
      simp [Verity.Core.Uint256.le_def] at hAmount' ⊢
      rw [hSubReq] at hAmount'
      omega
    have hSubAmt : ((totalAssets - amount : Uint256) : Nat) = (totalAssets : Nat) - (amount : Nat) := by
      exact sub_eq_of_le (by simpa [Verity.Core.Uint256.le_def] using hAmountLeAssets)
    simp [Verity.Core.Uint256.le_def]
    rw [hSubAmt]
    have hAvailNat : (required : Nat) < (totalAssets : Nat) := by
      simpa [Verity.Core.Uint256.lt_def] using hAvail
    have hAmountNat : (amount : Nat) <= ((totalAssets - required : Uint256) : Nat) := by
      simpa [Verity.Core.Uint256.le_def] using hAmount'
    rw [hSubReq] at hAmountNat
    omega
  · have hAmountLeZero : amount <= 0 := by
      simpa [satSub, hAvail] using hAmount
    have hAmountPos : 0 < (amount : Nat) := u256_nat_pos hPositive
    have hAmountZero : (amount : Nat) = 0 := by
      simp [Verity.Core.Uint256.le_def] at hAmountLeZero
      omega
    have : False := by omega
    exact False.elim this

/--
Executing a successful positive `borrow(amount)` leaves at least the required
liquidity in the market after the transfer.
-/
theorem positive_borrow_preserves_required_liquidity
    (amount : Uint256) (preState : ContractState)
    (hPositive : amount > 0)
    (hPre : borrow_succeeds_preconditions amount preState) :
    let postState := runBorrow amount preState;
    positive_borrow_preserves_required_liquidity_spec amount preState postState := by
  have hAssets : totalAssetsOf (runBorrow amount preState) = totalAssetsOf preState - amount := by
    exact borrow_total_assets_write amount preState hPre
  rcases hPre with ⟨_, _, _, _, _, _, _, _, _, hAmount⟩
  unfold positive_borrow_preserves_required_liquidity_spec
  constructor
  · exact hAssets
  · rw [hAssets]
    exact totalAssets_after_positive_borrow_ge_required
      amount
      (totalAssetsOf preState)
      (requiredLiquidityAfterUpdate preState)
      hPositive
      hAmount

end Benchmark.Cases.Wildcat.BorrowLiquiditySafety
