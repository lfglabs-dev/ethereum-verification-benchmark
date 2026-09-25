import Benchmark.Cases.Cow.GPv2Settlement.Specs

namespace Benchmark.Cases.Cow.GPv2Settlement

open Verity
open Verity.EVM.Uint256

/-- Over any tracked lifecycle of one order (trades, invalidations, storage frees, swap bookkeeping and unrelated steps), the settle-path trades counted since tracking began are never overfilled, respect the limit price together, and keep fees at most `feeAmount` pro rata. Swap fills are not counted and carry no price claim. -/
theorem order_lifecycle_safety (orderUid : Uint256) (o : SignedOrder)
    (s : ContractState) (t : OrderTotals)
    (h : OrderLifecycle orderUid o s t) : cumulative_order_safety_spec o t := by
  exact ?_

end Benchmark.Cases.Cow.GPv2Settlement
