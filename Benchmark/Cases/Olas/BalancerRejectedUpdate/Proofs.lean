import Benchmark.Cases.Olas.BalancerRejectedUpdate.Specs

namespace Benchmark.Cases.Olas.BalancerRejectedUpdate

theorem rejected_update_preserves_metadata
    (snapshot : PriceSnapshot) (elapsedTime : Nat) :
    rejected_update_preserves_metadata_spec snapshot elapsedTime := by
  simp [rejected_update_preserves_metadata_spec, rejectedUpdate]

theorem rejected_update_mutates_cumulative
    (snapshot : PriceSnapshot) (elapsedTime : Nat) :
    rejected_update_mutates_cumulative_spec snapshot elapsedTime := by
  simp [rejected_update_mutates_cumulative_spec, rejectedUpdate]

theorem repeated_rejection_double_counts
    (snapshot : PriceSnapshot) (firstElapsed secondElapsed : Nat) :
    repeated_rejection_double_counts_spec snapshot firstElapsed secondElapsed := by
  simp [repeated_rejection_double_counts_spec, rejectedUpdate, Nat.mul_add,
    Nat.add_assoc]

theorem rejected_update_corruption_witness :
    rejected_update_corruption_witness_spec := by
  norm_num [rejected_update_corruption_witness_spec, rejectedUpdate]

end Benchmark.Cases.Olas.BalancerRejectedUpdate
