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

theorem releaseClosedMarketCredit_preserves_accounting
    (s : RehypeAccounting) (hInv : rehypeFeeAccountingInvariant s) :
    rehypeFeeAccountingInvariant (releaseClosedMarketCredit s) := by
  rcases unpackInvariant hInv with ⟨hrx, hry, hcx, hcy, hox, hoy⟩
  simp [rehypeFeeAccountingInvariant, reservationMatchesCarry, creditCoversReservations, feeConservation,
    releaseClosedMarketCredit, carryX, carryY, totalReservedX, totalReservedY] at *
  omega

end Benchmark.Cases.Doppler.MulticurveFeeConservation
