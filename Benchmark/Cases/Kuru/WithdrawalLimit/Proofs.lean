/-
Kuru V2 complete withdrawal-policy reference proof bundle.
All eight complete specification groups are proved on the source-shaped Lean
model. Solidity correspondence is manually reviewed, not mechanized refinement.
-/
import Benchmark.Cases.Kuru.WithdrawalLimit.Proofs.WriterProofs

namespace Benchmark.Cases.Kuru.WithdrawalLimit

theorem exact_history_correspondence : ExactHistoryCorrespondence :=
  HistoryProofs.exactHistoryCorrespondence

theorem policy_bundle : PolicyBundle :=
  ⟨initialization_and_writer_closure,exact_history_correspondence,valuation_and_widths,
    transaction_and_snapshots,ordinary_and_global_no_reuse,drip_and_configuration,
    approved_authority_and_replay,payout_coverage_and_atomicity⟩

#print axioms initialization_and_writer_closure
#print axioms exact_history_correspondence
#print axioms valuation_and_widths
#print axioms transaction_and_snapshots
#print axioms ordinary_and_global_no_reuse
#print axioms drip_and_configuration
#print axioms approved_authority_and_replay
#print axioms payout_coverage_and_atomicity
#print axioms policy_bundle
#print axioms measured_deposit_credit
#print axioms measured_ordinary_settlement
#print axioms measured_approved_settlement
#print axioms core_transfer_debit
#print axioms core_refund_frame

end Benchmark.Cases.Kuru.WithdrawalLimit
