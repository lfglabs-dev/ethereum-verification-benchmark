import Benchmark.Cases.Doppler.MulticurveFeeConservation.Specs

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

set_option autoImplicit false

private theorem unpackInvariant {s : RehypeAccounting}
    (h : rehypeFeeAccountingInvariant s) :
    s.reservedX = carryX s ∧ s.reservedY = carryY s ∧
    totalReservedX s ≤ s.managerCreditX ∧ totalReservedY s ≤ s.managerCreditY ∧
    s.originX = carryX s + s.paidX + s.compoundedX ∧
    s.originY = carryY s + s.paidY + s.compoundedY := by
  rcases h with ⟨⟨hrx, hry⟩, ⟨hcx, hcy⟩, hox, hoy⟩
  exact ⟨hrx, hry, hcx, hcy, hox, hoy⟩

theorem onSwapFeeReceivedX_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee) :
    rehypeFeeAccountingInvariant (_onSwapFeeReceivedX s fee stay convert lp) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    _onSwapFeeReceivedX, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

theorem onSwapFeeReceivedY_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee) :
    rehypeFeeAccountingInvariant (_onSwapFeeReceivedY s fee stay convert lp) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    _onSwapFeeReceivedY, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

theorem processFees_fullyDeferred_preserves_accounting
    (s : RehypeAccounting) (hInv : rehypeFeeAccountingInvariant s) :
    rehypeFeeAccountingInvariant (processFeesDeferred s) := by
  simpa [processFeesDeferred] using hInv

theorem convertForwardXToY_partial_preserves_accounting
    (s : RehypeAccounting) (spent received : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : spent ≤ s.carry.toY.x) :
    rehypeFeeAccountingInvariant (convertForwardXToYAndSettle s spent received) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    convertForwardXToYAndSettle, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

theorem convertForwardYToX_partial_preserves_accounting
    (s : RehypeAccounting) (spent received : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : spent ≤ s.carry.toX.y) :
    rehypeFeeAccountingInvariant (convertForwardYToXAndSettle s spent received) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    convertForwardYToXAndSettle, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

/-- A callback that arrives during processing is written into next carry before
the snapshotted X budget residual is merged. Bounding `spent` by the pre-callback
row proves that the callback addition cannot be consumed by the old snapshot. -/
theorem callbackDuringProcessX_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.toY.x) :
    rehypeFeeAccountingInvariant
      (convertForwardXToYAndSettle
        (_onSwapFeeReceivedX s fee stay convert lp) spent received) := by
  have hCallback := onSwapFeeReceivedX_preserves_accounting s fee stay convert lp hInv hSplit
  apply convertForwardXToY_partial_preserves_accounting _ spent received hCallback
  simp [_onSwapFeeReceivedX]
  omega

/-- Y-denominated symmetric snapshot/callback composition. -/
theorem callbackDuringProcessY_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.toX.y) :
    rehypeFeeAccountingInvariant
      (convertForwardYToXAndSettle
        (_onSwapFeeReceivedY s fee stay convert lp) spent received) := by
  have hCallback := onSwapFeeReceivedY_preserves_accounting s fee stay convert lp hInv hSplit
  apply convertForwardYToX_partial_preserves_accounting _ spent received hCallback
  simp [_onSwapFeeReceivedY]
  omega

theorem settleMarketForwards_preserves_accounting
    (s : RehypeAccounting) (forwardedX forwardedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hx : forwardedX ≤ s.carry.toX.x)
    (hy : forwardedY ≤ s.carry.toY.y) :
    rehypeFeeAccountingInvariant (_settleMarketForwards s forwardedX forwardedY) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    _settleMarketForwards, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

theorem compoundLiquiditySellX_partial_preserves_accounting
    (s : RehypeAccounting) (spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : spent ≤ s.carry.lp.x)
    (hProvideX : providedX ≤ s.carry.lp.x - spent)
    (hProvideY : providedY ≤ s.carry.lp.y + received) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellX s spent received providedX providedY) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    _compoundLiquiditySellX, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

theorem compoundLiquiditySellY_partial_preserves_accounting
    (s : RehypeAccounting) (spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : spent ≤ s.carry.lp.y)
    (hProvideX : providedX ≤ s.carry.lp.x + received)
    (hProvideY : providedY ≤ s.carry.lp.y - spent) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellY s spent received providedX providedY) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    _compoundLiquiditySellY, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

/-- An X callback written into next carry cannot be consumed by the old
same-token-forward snapshot. -/
theorem callbackXThenSettleOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp forwardedX forwardedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hForwardedX : forwardedX ≤ s.carry.toX.x)
    (hForwardedY : forwardedY ≤ s.carry.toY.y) :
    rehypeFeeAccountingInvariant
      (_settleMarketForwards
        (_onSwapFeeReceivedX s fee stay convert lp) forwardedX forwardedY) := by
  have hCallback := onSwapFeeReceivedX_preserves_accounting s fee stay convert lp hInv hSplit
  apply settleMarketForwards_preserves_accounting _ forwardedX forwardedY hCallback
  · simp [_onSwapFeeReceivedX]
    omega
  · simp [_onSwapFeeReceivedX]
    omega

/-- Y-denominated symmetric same-token-forward snapshot composition. -/
theorem callbackYThenSettleOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp forwardedX forwardedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hForwardedX : forwardedX ≤ s.carry.toX.x)
    (hForwardedY : forwardedY ≤ s.carry.toY.y) :
    rehypeFeeAccountingInvariant
      (_settleMarketForwards
        (_onSwapFeeReceivedY s fee stay convert lp) forwardedX forwardedY) := by
  have hCallback := onSwapFeeReceivedY_preserves_accounting s fee stay convert lp hInv hSplit
  apply settleMarketForwards_preserves_accounting _ forwardedX forwardedY hCallback
  · simp [_onSwapFeeReceivedY]
    omega
  · simp [_onSwapFeeReceivedY]
    omega

/-- X callback plus an old X-selling LP snapshot. All spend/provide bounds are
against pre-callback LP carry, so next-carry additions survive. -/
theorem callbackXThenCompoundSellXOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.lp.x)
    (hProvideX : providedX ≤ s.carry.lp.x - spent)
    (hProvideY : providedY ≤ s.carry.lp.y + received) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellX
        (_onSwapFeeReceivedX s fee stay convert lp) spent received providedX providedY) := by
  have hCallback := onSwapFeeReceivedX_preserves_accounting s fee stay convert lp hInv hSplit
  apply compoundLiquiditySellX_partial_preserves_accounting
    _ spent received providedX providedY hCallback
  · simp [_onSwapFeeReceivedX]
    omega
  · simp [_onSwapFeeReceivedX]
    omega
  · simp [_onSwapFeeReceivedX]
    omega

/-- X callback plus an old Y-selling LP snapshot. -/
theorem callbackXThenCompoundSellYOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.lp.y)
    (hProvideY : providedY ≤ s.carry.lp.y - spent)
    (hProvideX : providedX ≤ s.carry.lp.x + received) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellY
        (_onSwapFeeReceivedX s fee stay convert lp) spent received providedX providedY) := by
  have hCallback := onSwapFeeReceivedX_preserves_accounting s fee stay convert lp hInv hSplit
  apply compoundLiquiditySellY_partial_preserves_accounting
    _ spent received providedX providedY hCallback
  · simp [_onSwapFeeReceivedX]
    omega
  · simp [_onSwapFeeReceivedX]
    omega
  · simp [_onSwapFeeReceivedX]
    omega

/-- Y callback plus an old X-selling LP snapshot. -/
theorem callbackYThenCompoundSellXOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.lp.x)
    (hProvideX : providedX ≤ s.carry.lp.x - spent)
    (hProvideY : providedY ≤ s.carry.lp.y + received) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellX
        (_onSwapFeeReceivedY s fee stay convert lp) spent received providedX providedY) := by
  have hCallback := onSwapFeeReceivedY_preserves_accounting s fee stay convert lp hInv hSplit
  apply compoundLiquiditySellX_partial_preserves_accounting
    _ spent received providedX providedY hCallback
  · simp [_onSwapFeeReceivedY]
    omega
  · simp [_onSwapFeeReceivedY]
    omega
  · simp [_onSwapFeeReceivedY]
    omega

/-- Y callback plus an old Y-selling LP snapshot. -/
theorem callbackYThenCompoundSellYOldSnapshot_preserves_accounting
    (s : RehypeAccounting) (fee stay convert lp spent received providedX providedY : Nat)
    (hInv : rehypeFeeAccountingInvariant s)
    (hSplit : stay + convert + lp = fee)
    (hSpent : spent ≤ s.carry.lp.y)
    (hProvideY : providedY ≤ s.carry.lp.y - spent)
    (hProvideX : providedX ≤ s.carry.lp.x + received) :
    rehypeFeeAccountingInvariant
      (_compoundLiquiditySellY
        (_onSwapFeeReceivedY s fee stay convert lp) spent received providedX providedY) := by
  have hCallback := onSwapFeeReceivedY_preserves_accounting s fee stay convert lp hInv hSplit
  apply compoundLiquiditySellY_partial_preserves_accounting
    _ spent received providedX providedY hCallback
  · simp [_onSwapFeeReceivedY]
    omega
  · simp [_onSwapFeeReceivedY]
    omega
  · simp [_onSwapFeeReceivedY]
    omega

private theorem applyForwardToX_preserves_accounting
    {s : RehypeAccounting} {o : ForwardLegOutcome}
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : match o with
      | .deferred => True
      | .converted spent _ => spent ≤ s.carry.toX.y) :
    rehypeFeeAccountingInvariant (applyForwardToX s o) := by
  cases o with
  | deferred => simpa [applyForwardToX] using hInv
  | converted spent received =>
      exact convertForwardYToX_partial_preserves_accounting s spent received hInv hSpent

private theorem applyForwardToY_preserves_accounting
    {s : RehypeAccounting} {o : ForwardLegOutcome}
    (hInv : rehypeFeeAccountingInvariant s)
    (hSpent : match o with
      | .deferred => True
      | .converted spent _ => spent ≤ s.carry.toY.x) :
    rehypeFeeAccountingInvariant (applyForwardToY s o) := by
  cases o with
  | deferred => simpa [applyForwardToY] using hInv
  | converted spent received =>
      exact convertForwardXToY_partial_preserves_accounting s spent received hInv hSpent

private theorem applyLpLeg_preserves_accounting
    {s : RehypeAccounting} {o : LpLegOutcome}
    (hInv : rehypeFeeAccountingInvariant s)
    (hBounds : match o with
      | .deferred => True
      | .sellX spent received providedX providedY _ =>
          spent ≤ s.carry.lp.x ∧ providedX ≤ s.carry.lp.x - spent ∧ providedY ≤ s.carry.lp.y + received
      | .sellY spent received providedX providedY _ =>
          spent ≤ s.carry.lp.y ∧ providedX ≤ s.carry.lp.x + received ∧ providedY ≤ s.carry.lp.y - spent) :
    rehypeFeeAccountingInvariant (applyLpLeg s o) := by
  cases o with
  | deferred => simpa [applyLpLeg] using hInv
  | sellX spent received providedX providedY liquidityAdded =>
      exact compoundLiquiditySellX_partial_preserves_accounting
        s spent received providedX providedY hInv hBounds.1 hBounds.2.1 hBounds.2.2
  | sellY spent received providedX providedY liquidityAdded =>
      exact compoundLiquiditySellY_partial_preserves_accounting
        s spent received providedX providedY hInv hBounds.1 hBounds.2.1 hBounds.2.2

private theorem applyForwardToX_leaves_toYInX
    (s : RehypeAccounting) (o : ForwardLegOutcome) :
    (applyForwardToX s o).carry.toY.x = s.carry.toY.x := by
  cases o <;> rfl

private theorem applyForwardToX_leaves_lp
    (s : RehypeAccounting) (o : ForwardLegOutcome) :
    (applyForwardToX s o).carry.lp = s.carry.lp := by
  cases o <;> rfl

private theorem applyForwardToY_leaves_lp
    (s : RehypeAccounting) (o : ForwardLegOutcome) :
    (applyForwardToY s o).carry.lp = s.carry.lp := by
  cases o <;> rfl

/-- Mechanical witness that the source Boolean may be false after the LP
balancing-swap branch succeeds but provision returns zero liquidity. -/
private theorem processFeesProcessed_false_after_balancing_swap
    (s : RehypeAccounting) (spent received : Nat)
    (hSameX : s.carry.toX.x = 0) (hSameY : s.carry.toY.y = 0) :
    let p : ProcessFeesPlan := {
      callbackFeeX := 0, callbackStayX := 0, callbackConvertX := 0, callbackLpX := 0,
      callbackFeeY := 0, callbackStayY := 0, callbackConvertY := 0, callbackLpY := 0,
      forwardToX := .deferred, forwardToY := .deferred,
      lp := .sellX spent received 0 0 0 }
    processFeesProcessed s p = false := by
  simp [processFeesProcessed, forwardReceived, lpLiquidityAdded, hSameX, hSameY]

/-- Finite modeled `processFees` accounting-outcome composition, including
independent forward success/defer outcomes, all LP outcomes, callback merge,
and both Boolean results. This does not prove source-branch reachability. -/
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
  let s0 := _settleMarketForwards s s.carry.toX.x s.carry.toY.y
  have h0 : rehypeFeeAccountingInvariant s0 := by
    exact settleMarketForwards_preserves_accounting s s.carry.toX.x s.carry.toY.y hInv (by omega) (by omega)
  have hForwardToX0 : match p.forwardToX with
      | .deferred => True
      | .converted spent _ => spent ≤ s0.carry.toX.y := by
    simpa [s0, _settleMarketForwards] using hForwardToX
  let s1 := applyForwardToX s0 p.forwardToX
  have h1 : rehypeFeeAccountingInvariant s1 := applyForwardToX_preserves_accounting h0 hForwardToX0
  have hForwardToY1 : match p.forwardToY with
      | .deferred => True
      | .converted spent _ => spent ≤ s1.carry.toY.x := by
    simpa [s1, applyForwardToX_leaves_toYInX, s0, _settleMarketForwards] using hForwardToY
  let s2 := applyForwardToY s1 p.forwardToY
  have h2 : rehypeFeeAccountingInvariant s2 := applyForwardToY_preserves_accounting h1 hForwardToY1
  have hLp2 : match p.lp with
      | .deferred => True
      | .sellX spent received providedX providedY _ =>
          spent ≤ s2.carry.lp.x ∧ providedX ≤ s2.carry.lp.x - spent ∧ providedY ≤ s2.carry.lp.y + received
      | .sellY spent received providedX providedY _ =>
          spent ≤ s2.carry.lp.y ∧ providedX ≤ s2.carry.lp.x + received ∧ providedY ≤ s2.carry.lp.y - spent := by
    simpa [s2, applyForwardToY_leaves_lp, s1, applyForwardToX_leaves_lp,
      s0, _settleMarketForwards] using hLp
  let s3 := applyLpLeg s2 p.lp
  have h3 : rehypeFeeAccountingInvariant s3 := applyLpLeg_preserves_accounting h2 hLp2
  let s4 := _onSwapFeeReceivedX s3 p.callbackFeeX p.callbackStayX p.callbackConvertX p.callbackLpX
  have h4 : rehypeFeeAccountingInvariant s4 :=
    onSwapFeeReceivedX_preserves_accounting s3 p.callbackFeeX p.callbackStayX
      p.callbackConvertX p.callbackLpX h3 (by omega)
  have h5 : rehypeFeeAccountingInvariant
      (_onSwapFeeReceivedY s4 p.callbackFeeY p.callbackStayY p.callbackConvertY p.callbackLpY) :=
    onSwapFeeReceivedY_preserves_accounting s4 p.callbackFeeY p.callbackStayY
      p.callbackConvertY p.callbackLpY h4 (by omega)
  simpa [processFeesStep, s0, s1, s2, s3, s4] using h5

theorem releaseClosedMarketCredit_preserves_accounting
    (s : RehypeAccounting) (hInv : rehypeFeeAccountingInvariant s) :
    rehypeFeeAccountingInvariant (releaseClosedMarketCredit s) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    releaseClosedMarketCredit, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

end Benchmark.Cases.Doppler.MulticurveFeeConservation
