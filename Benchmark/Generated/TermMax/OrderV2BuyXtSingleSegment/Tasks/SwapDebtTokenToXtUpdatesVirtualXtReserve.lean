import Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment.Specs

namespace Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment

open Verity
open Verity.EVM.Uint256

/--
Executing the single-segment exact-input `debtToken -> XT` pricing path updates
`virtualXtReserve` by exactly the curve-computed XT output amount.
-/
theorem swapDebtTokenToXt_updates_virtual_xt_reserve
    (daysToMaturity debtTokenAmtIn minTokenOut : Uint256)
    (borrowTakerFeeRatio lendMakerFeeRatio : Uint256)
    (cutLiqSquare : Uint256) (cutOffset : Int256)
    (s : ContractState)
    (hNonZeroInput : debtTokenAmtIn != 0)
    (hLockOpen : s.storage 1 = 0)
    (hVXtNonZero : plusInt256 (s.storage 0) cutOffset != 0)
    (hNoCross :
      singleSegmentBuyXtTokenAmtOut
          daysToMaturity
          (s.storage 0)
          debtTokenAmtIn
          borrowTakerFeeRatio
          cutLiqSquare
          cutOffset
        <= s.storage 0)
    (hMinOut :
      add
          (singleSegmentBuyXtTokenAmtOut
            daysToMaturity
            (s.storage 0)
            debtTokenAmtIn
            borrowTakerFeeRatio
            cutLiqSquare
            cutOffset)
          debtTokenAmtIn
        >= minTokenOut) :
    let s' := ((
      TermMaxOrderV2BuyXtSingleSegment.swapDebtTokenToXtExactInSingleSegment
        debtTokenAmtIn
        minTokenOut
        daysToMaturity
        borrowTakerFeeRatio
        lendMakerFeeRatio
        cutLiqSquare
        cutOffset
      ).run s).snd
    swapDebtTokenToXt_updates_virtual_xt_reserve_spec
      daysToMaturity
      debtTokenAmtIn
      borrowTakerFeeRatio
      cutLiqSquare
      cutOffset
      s
      s' := by
  exact ?_

end Benchmark.Cases.TermMax.OrderV2BuyXtSingleSegment
