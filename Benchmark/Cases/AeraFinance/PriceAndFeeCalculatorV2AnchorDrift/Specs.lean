import Verity.Specs.Common
import Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift.Contract

namespace Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift

open Verity
open Verity.EVM.Uint256

def pausedOf (s : ContractState) : Uint256 := s.storage 0
def pauseOnBadAnchorUpdateOf (s : ContractState) : Uint256 := s.storage 1
def anchorPriceOf (s : ContractState) : Uint256 := s.storage 2
def anchorTimestampOf (s : ContractState) : Uint256 := s.storage 3
def driftPriceOf (s : ContractState) : Uint256 := s.storage 4
def driftTimestampOf (s : ContractState) : Uint256 := s.storage 5
def minPriceToleranceRatioOf (s : ContractState) : Uint256 := s.storage 6
def maxPriceToleranceRatioOf (s : ContractState) : Uint256 := s.storage 7
def accrualLagOf (s : ContractState) : Uint256 := s.storage 8

/-- Natural-number interpretation of the source's non-overflowing uint128/uint16
    anchor-band arithmetic. -/
def priceWithinAnchorBand (s : ContractState) (anchor candidate : Uint256) : Prop :=
  if candidate > anchor then
    candidate.val * 10000 <= anchor.val * (maxPriceToleranceRatioOf s).val
  else
    candidate.val * 10000 >= anchor.val * (minPriceToleranceRatioOf s).val

/-- The three word products used by the source retain their natural values. The
    Solidity uint128 prices and uint16 ratios establish these equalities. -/
def anchorBandProductsExact (s : ContractState) (anchor candidate : Uint256) : Prop :=
  (mul candidate 10000).val = candidate.val * 10000 ∧
  (mul anchor (maxPriceToleranceRatioOf s)).val =
    anchor.val * (maxPriceToleranceRatioOf s).val ∧
  (mul anchor (minPriceToleranceRatioOf s)).val =
    anchor.val * (minPriceToleranceRatioOf s).val

/-- A successful drift update is stored inside the previous anchor band and does
    not mutate the anchor tuple. -/
def drift_update_preserves_anchor_band_spec
    (price timestamp : Uint256) (s : ContractState) : Prop :=
  let result := (AeraPriceAndFeeCalculatorV2.setDriftPrice price timestamp true true).run s
  let s' := result.snd
  result = ContractResult.success () s' ∧
    priceWithinAnchorBand s (anchorPriceOf s) price ∧
    anchorPriceOf s' = anchorPriceOf s ∧
    anchorTimestampOf s' = anchorTimestampOf s ∧
    driftPriceOf s' = price ∧
    driftTimestampOf s' = timestamp

/-- A policy-violating anchor update in pause mode pauses the vault and records
    the new anchor tuple, matching the source's fail-safe branch. -/
def bad_anchor_pause_mode_spec
    (price timestamp : Uint256) (s : ContractState) : Prop :=
  let result := (AeraPriceAndFeeCalculatorV2.setAnchorPrice price timestamp true true true).run s
  let s' := result.snd
  result = ContractResult.success () s' ∧
    pausedOf s' = 1 ∧
    anchorPriceOf s' = price ∧
    anchorTimestampOf s' = timestamp ∧
    accrualLagOf s' = sub timestamp (anchorTimestampOf s)

/-- If pause-on-bad-anchor is disabled, the same policy violation reverts and
    preserves the complete input state. -/
def bad_anchor_revert_mode_spec
    (price timestamp : Uint256) (s : ContractState) : Prop :=
  (AeraPriceAndFeeCalculatorV2.setAnchorPrice price timestamp true true true).run s =
    ContractResult.revert "BadAnchorPriceUpdate" s

end Benchmark.Cases.AeraFinance.PriceAndFeeCalculatorV2AnchorDrift
