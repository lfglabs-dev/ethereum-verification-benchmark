import Benchmark.Grindset
import Benchmark.Cases.Olas.BalancerRejectedUpdate.Specs
namespace Benchmark.Cases.Olas.BalancerRejectedUpdate
theorem repeated_rejection_double_counts (snapshot : PriceSnapshot)
    (firstElapsed secondElapsed : Nat) :
    repeated_rejection_double_counts_spec snapshot firstElapsed secondElapsed := by
  exact ?_
end Benchmark.Cases.Olas.BalancerRejectedUpdate
