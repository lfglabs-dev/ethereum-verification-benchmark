import Benchmark.Cases.Olas.BalancerRejectedUpdate.Contract

namespace Benchmark.Cases.Olas.BalancerRejectedUpdate

/-- A rejected call leaves the average and timestamp unchanged. -/
def rejected_update_preserves_metadata_spec
    (snapshot : PriceSnapshot) (elapsedTime : Nat) : Prop :=
  let after := rejectedUpdate snapshot elapsedTime
  after.averagePrice = snapshot.averagePrice ∧
  after.lastUpdated = snapshot.lastUpdated

/-- Despite returning false, the rejected branch persists one elapsed-price term. -/
def rejected_update_mutates_cumulative_spec
    (snapshot : PriceSnapshot) (elapsedTime : Nat) : Prop :=
  (rejectedUpdate snapshot elapsedTime).cumulativePrice =
    snapshot.cumulativePrice + snapshot.averagePrice * elapsedTime

/-- Two rejected calls count both elapsed intervals while retaining the old timestamp. -/
def repeated_rejection_double_counts_spec
    (snapshot : PriceSnapshot) (firstElapsed secondElapsed : Nat) : Prop :=
  (rejectedUpdate (rejectedUpdate snapshot firstElapsed) secondElapsed).cumulativePrice =
    snapshot.cumulativePrice + snapshot.averagePrice * (firstElapsed + secondElapsed)

/-- Concrete report witness: 10,000 becomes 40,000 instead of 30,000. -/
def rejected_update_corruption_witness_spec : Prop :=
  let initial : PriceSnapshot := {
    cumulativePrice := 10000, averagePrice := 100, lastUpdated := 0
  }
  let afterFirst := rejectedUpdate initial 100
  let afterSecond := rejectedUpdate afterFirst 200
  afterFirst.cumulativePrice = 20000 ∧
  afterSecond.cumulativePrice = 40000 ∧
  (initial.cumulativePrice + initial.averagePrice * 200) = 30000

end Benchmark.Cases.Olas.BalancerRejectedUpdate
