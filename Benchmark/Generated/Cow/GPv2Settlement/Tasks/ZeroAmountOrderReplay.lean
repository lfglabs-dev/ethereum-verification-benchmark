import Benchmark.Cases.Cow.GPv2Settlement.Specs

namespace Benchmark.Cases.Cow.GPv2Settlement

open Verity
open Verity.EVM.Uint256

/-- Witness for CoW's documented known issue: a fill-or-kill sell order with zero amounts and fee 1 can be executed twice from the same state, computing the full fee each time. Token movements are not modeled. -/
theorem zero_amount_order_replay (s : ContractState)
    (hTime : s.blockTimestamp.val ≤ 100)
    (hFilled : s.storageMapUint GPv2Settlement.filledAmount.slot 7 = 0) :
    (tradeCall 7 zeroAmountSellOrder 1 1 0).run s = ContractResult.success (1, 0, 1) s ∧
    OrderLifecycle 7 zeroAmountSellOrder s ⟨0, 0, 2⟩ ∧
    ¬ (⟨0, 0, 2⟩ : OrderTotals).fee ≤ zeroAmountSellOrder.feeAmount.val := by
  exact ?_

end Benchmark.Cases.Cow.GPv2Settlement
