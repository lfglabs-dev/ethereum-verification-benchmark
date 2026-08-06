import Benchmark.Cases.Monetrix.PMBorrowAccounting.Contract

namespace Benchmark.Cases.Monetrix.PMBorrowAccounting

/-- The source reader's return value is independent of both borrow fields. -/
def reader_omits_borrow_spec (pm : PMState) : Prop :=
  suppliedBalance pm = pm.supplyValue

/-- Reported surplus exceeds liability-aware surplus by exactly the omitted borrow. -/
def surplus_overstatement_spec (otherBacking : Int) (pm : PMState)
    (usdmSupply redemptionShortfall : Int) : Prop :=
  reportedSurplus otherBacking pm usdmSupply redemptionShortfall =
    netSurplus otherBacking pm usdmSupply redemptionShortfall + pm.borrowValue

/-- A source-reachable accounting witness can pass Gate 3 while net surplus is negative. -/
def phantom_surplus_witness_spec : Prop :=
  let pm : PMState := {
    borrowBasis := 0, borrowValue := 80,
    supplyBasis := 0, supplyValue := 100
  }
  reportedSurplus 0 pm 50 0 = 50 ∧
  netSurplus 0 pm 50 0 = -30 ∧
  settlementGate3 (reportedSurplus 0 pm 50 0) 10 ∧
  ¬ settlementGate3 (netSurplus 0 pm 50 0) 10

end Benchmark.Cases.Monetrix.PMBorrowAccounting
