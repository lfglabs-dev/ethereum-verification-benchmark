import Benchmark.Cases.Monetrix.PMBorrowAccounting.Specs

namespace Benchmark.Cases.Monetrix.PMBorrowAccounting

/-- The audited decoder returns supply only, regardless of PM borrow state. -/
theorem suppliedBalance_returns_supply (pm : PMState) :
    reader_omits_borrow_spec pm := by
  rfl

/-- The source's surplus overstatement is exactly the omitted borrow liability. -/
theorem reported_surplus_overstates_by_borrow
    (otherBacking : Int) (pm : PMState)
    (usdmSupply redemptionShortfall : Int) :
    surplus_overstatement_spec otherBacking pm usdmSupply redemptionShortfall := by
  unfold surplus_overstatement_spec reportedSurplus netSurplus
    reportedBacking netBacking suppliedBalance
  ring

/-- Concrete witness: source Gate 3 sees +50 while liability-aware surplus is -30. -/
theorem phantom_surplus_gate_witness : phantom_surplus_witness_spec := by
  norm_num [phantom_surplus_witness_spec, reportedSurplus, netSurplus,
    reportedBacking, netBacking, suppliedBalance, settlementGate3]

end Benchmark.Cases.Monetrix.PMBorrowAccounting
