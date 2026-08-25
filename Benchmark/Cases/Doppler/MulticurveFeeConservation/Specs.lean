import Benchmark.Cases.Doppler.MulticurveFeeConservation.Contract

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

/-- INV-REH-1's per-market reservation identity. -/
def reservationMatchesCarry (s : RehypeAccounting) : Prop :=
  s.reservedX = carryX s ∧ s.reservedY = carryY s

/-- INV-REH-1's token-wide live-credit coverage at settled boundaries. -/
def creditCoversReservations (s : RehypeAccounting) : Prop :=
  totalReservedX s ≤ s.managerCreditX ∧ totalReservedY s ≤ s.managerCreditY

/--
Fee conservation by current denomination: every credited fee unit is either
still carried, already paid to beneficiaries, or already consumed by LP
provision. Conversion changes the denomination ledger by the exact DAMM
`spent`/`received` result before settlement.
-/
def feeConservation (s : RehypeAccounting) : Prop :=
  s.originX = carryX s + s.paidX + s.compoundedX ∧
  s.originY = carryY s + s.paidY + s.compoundedY

/-- Complete scoped accounting invariant: both halves of INV-REH-1 plus the
terminal carry/paid/compounded partition required by the fee-conservation
property. -/
def rehypeFeeAccountingInvariant (s : RehypeAccounting) : Prop :=
  reservationMatchesCarry s ∧ creditCoversReservations s ∧ feeConservation s

end Benchmark.Cases.Doppler.MulticurveFeeConservation
