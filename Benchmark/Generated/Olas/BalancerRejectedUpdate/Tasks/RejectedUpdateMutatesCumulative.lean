import Benchmark.Grindset
import Benchmark.Cases.Olas.BalancerRejectedUpdate.Specs
namespace Benchmark.Cases.Olas.BalancerRejectedUpdate
theorem rejected_update_mutates_cumulative (snapshot : PriceSnapshot) (elapsedTime : Nat) :
    rejected_update_mutates_cumulative_spec snapshot elapsedTime := by
  exact ?_
end Benchmark.Cases.Olas.BalancerRejectedUpdate
