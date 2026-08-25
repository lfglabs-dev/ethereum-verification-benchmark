import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

theorem processFeesStep_preserves_accounting
    (s : RehypeAccounting) (p : ProcessFeesPlan)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplitX : p.callbackFeeX = p.callbackStayX + p.callbackConvertX + p.callbackLpX)
    (hSplitY : p.callbackFeeY = p.callbackStayY + p.callbackConvertY + p.callbackLpY)
    (hForwardToX : match p.forwardToX with
      | .deferred => True
      | .converted spent _ => spent ≤ s.carry.toX.y)
    (hForwardToY : match p.forwardToY with
      | .deferred => True
      | .converted spent _ => spent ≤ s.carry.toY.x)
    (hLp : match p.lp with
      | .deferred => True
      | .sellX spent received providedX providedY _ =>
          spent ≤ s.carry.lp.x ∧ providedX ≤ s.carry.lp.x - spent ∧ providedY ≤ s.carry.lp.y + received
      | .sellY spent received providedX providedY _ =>
          spent ≤ s.carry.lp.y ∧ providedX ≤ s.carry.lp.x + received ∧ providedY ≤ s.carry.lp.y - spent) :
    rehypeFeeAccountingInvariant (processFeesStep s p).2 := by
  exact ?_

end Benchmark.Cases.Doppler.MulticurveFeeConservation
