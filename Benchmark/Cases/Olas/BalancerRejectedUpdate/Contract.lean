import Contracts.Common

namespace Benchmark.Cases.Olas.BalancerRejectedUpdate

/-
  Focused model of Code4rena 2026-01 Olas H-11.

  In the audited `BalancerPriceOracle.updatePrice`, the contract first executes
  `snapshot.cumulativePrice += snapshot.averagePrice * elapsedTime`. If the
  subsequent slippage check rejects the current price, it returns `false`
  without updating `averagePrice` or `lastUpdated`. A later call therefore uses
  elapsed time from the same old timestamp and counts the earlier interval again.

  The branch is modeled after the slippage predicate has evaluated to rejection.
  Checked uint256 overflow and the external Balancer price read are out of scope;
  values use unbounded naturals so the task isolates the write-ordering defect.
-/

structure PriceSnapshot where
  cumulativePrice : Nat
  averagePrice : Nat
  lastUpdated : Nat
  deriving Repr, DecidableEq

/-- State transition on the source's rejected-slippage branch. -/
def rejectedUpdate (snapshot : PriceSnapshot) (elapsedTime : Nat) : PriceSnapshot :=
  { snapshot with
      cumulativePrice := snapshot.cumulativePrice + snapshot.averagePrice * elapsedTime }

/-- Expected state if a rejected update had no persistent accounting effect. -/
def rejectedUpdateExpected (snapshot : PriceSnapshot) : PriceSnapshot := snapshot

end Benchmark.Cases.Olas.BalancerRejectedUpdate
