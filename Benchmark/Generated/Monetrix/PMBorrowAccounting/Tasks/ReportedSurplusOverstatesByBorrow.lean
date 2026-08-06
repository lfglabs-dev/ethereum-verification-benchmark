import Benchmark.Grindset
import Benchmark.Cases.Monetrix.PMBorrowAccounting.Specs
namespace Benchmark.Cases.Monetrix.PMBorrowAccounting
theorem reported_surplus_overstates_by_borrow (otherBacking : Int) (pm : PMState)
    (usdmSupply redemptionShortfall : Int) :
    surplus_overstatement_spec otherBacking pm usdmSupply redemptionShortfall := by
  exact ?_
end Benchmark.Cases.Monetrix.PMBorrowAccounting
