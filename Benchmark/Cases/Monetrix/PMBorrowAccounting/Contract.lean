import Contracts.Common

namespace Benchmark.Cases.Monetrix.PMBorrowAccounting

/-
  Focused model of Code4rena 2026-04 Monetrix M-01.

  The HyperCore 0x811 response contains borrow and supply fields. The audited
  `PrecompileReader.suppliedBalance` returns only the fourth field, `supplyValue`.
  `MonetrixAccountant._readL1Backing` then credits that value without subtracting
  `borrowValue`.

  This slice models the decoded economic values as `Int`, after the source's
  uint64-to-int256 conversion. Unit conversion and non-USDC oracle valuation are
  outside scope; all values are assumed to have already been normalized to the
  accountant's common 6-decimal USDC unit.
-/

structure PMState where
  borrowBasis : Int
  borrowValue : Int
  supplyBasis : Int
  supplyValue : Int
  deriving Repr, DecidableEq

/-- Source behavior of `PrecompileReader.suppliedBalance`: only field four is returned. -/
def suppliedBalance (pm : PMState) : Int := pm.supplyValue

/-- Backing reported by the audited accountant for one normalized PM slot. -/
def reportedBacking (otherBacking : Int) (pm : PMState) : Int :=
  otherBacking + suppliedBalance pm

/-- Economic net backing when the same PM slot's borrow liability is included. -/
def netBacking (otherBacking : Int) (pm : PMState) : Int :=
  otherBacking + pm.supplyValue - pm.borrowValue

/-- Source-facing distributable surplus used by settlement Gate 3. -/
def reportedSurplus (otherBacking : Int) (pm : PMState)
    (usdmSupply redemptionShortfall : Int) : Int :=
  reportedBacking otherBacking pm - usdmSupply - redemptionShortfall

/-- Liability-aware surplus for comparison with the source calculation. -/
def netSurplus (otherBacking : Int) (pm : PMState)
    (usdmSupply redemptionShortfall : Int) : Int :=
  netBacking otherBacking pm - usdmSupply - redemptionShortfall

/-- The economically relevant part of settlement Gate 3. -/
def settlementGate3 (surplus proposedYield : Int) : Prop :=
  surplus > 0 ∧ proposedYield ≥ 0 ∧ proposedYield ≤ surplus

end Benchmark.Cases.Monetrix.PMBorrowAccounting
