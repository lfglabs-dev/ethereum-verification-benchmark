import Benchmark.Cases.Cow.GPv2Settlement.Specs

namespace Benchmark.Cases.Cow.GPv2Settlement

open Verity
open Verity.EVM.Uint256

/-- For an order with a nonzero limit amount, the total computed fee of settle-path trades since tracking began never exceeds `feeAmount`. Token movements and swap fee transfers are not modeled. -/
theorem order_lifecycle_fee_cap (orderUid : Uint256) (o : SignedOrder)
    (s : ContractState) (t : OrderTotals)
    (h : OrderLifecycle orderUid o s t) : total_fee_cap_spec o t := by
  exact ?_

end Benchmark.Cases.Cow.GPv2Settlement
