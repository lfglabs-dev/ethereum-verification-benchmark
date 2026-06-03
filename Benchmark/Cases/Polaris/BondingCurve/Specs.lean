import Verity.Specs.Common
import Benchmark.Cases.Polaris.BondingCurve.Contract

namespace Benchmark.Cases.Polaris.BondingCurve

open Verity
open Verity.EVM.Uint256

def virtualBalanceOf (s : ContractState) : Uint256 := s.storage 0
def floorSupplyOf (s : ContractState) : Uint256 := s.storage 1
def floorBalanceOf (s : ContractState) : Uint256 := s.storage 2
def totalSupplyOf (s : ContractState) : Uint256 := s.storage 3
def feePercentageOf (s : ContractState) : Uint256 := s.storage 4
def initializedOf (s : ContractState) : Uint256 := s.storage 5
def alphaOf (s : ContractState) : Uint256 := s.storage 6
def bPlusOneOf (s : ContractState) : Uint256 := s.storage 7

def curveBalanceAt (s : ContractState) (supply : Uint256) : Uint256 :=
  getBalanceFromReserveRatio (alphaOf s) (bPlusOneOf s) supply

/--
  Narrow residual math boundary: the executable model receives only the raw
  fixed-point pow result because `verity_contract` cannot call opaque Lean
  helpers in the function body. The helper's multiplication and
  `(left + DECIMAL_PRECISION - 1) / B_PLUS_1` division are modeled directly.
-/
def trustedCurvePowOutput (s : ContractState) (supply powOut : Uint256) : Prop :=
  powOut = curvePow supply (bPlusOneOf s)

/-- Source helper: `virtualSupply() = floorSupply + totalSupply()`. -/
def virtualSupplyOf (s : ContractState) : Uint256 :=
  add (floorSupplyOf s) (totalSupplyOf s)

def sellFeeAmount (bcTokenAmount : Uint256) (s : ContractState) : Uint256 :=
  div (mul bcTokenAmount (feePercentageOf s)) decimalPrecision

def sellNetBurnAmount (bcTokenAmount : Uint256) (s : ContractState) : Uint256 :=
  sub bcTokenAmount (sellFeeAmount bcTokenAmount s)

/--
  `sell` first burns the net amount from the seller. The sell fee is transferred
  to the fee router and may later be burned through `floorSellAndBurn`; that burn
  reduces aggregate `totalSupply` while increasing `floorSupply`, so the current
  virtual supply remains the post-sell supply below.
-/
def sellVirtualSupplyAfter (bcTokenAmount : Uint256) (s : ContractState) : Uint256 :=
  sub (virtualSupplyOf s) (sellNetBurnAmount bcTokenAmount s)

def floorSupplyAfterFeeBurn (bcTokenAmount : Uint256) (s : ContractState) : Uint256 :=
  add (floorSupplyOf s) bcTokenAmount

def totalSupplyAfterFeeBurn (bcTokenAmount : Uint256) (s : ContractState) : Uint256 :=
  sub (totalSupplyOf s) bcTokenAmount

def virtualSupplyAfterFeeBurn (bcTokenAmount : Uint256) (s : ContractState) : Uint256 :=
  add (floorSupplyAfterFeeBurn bcTokenAmount s) (totalSupplyAfterFeeBurn bcTokenAmount s)

/--
  Readable form of `reserveRatioDeviation(virtualSupply(), virtualBalance) == 0`.
  The model computes the source-shaped reserve helper directly, except for the
  low-level opaque `curvePow` boundary.
-/
def currentReserveRatioDeviationZero (s : ContractState) : Prop :=
  virtualBalanceOf s = curveBalanceAt s (virtualSupplyOf s)

/--
  Readable form of `reserveRatioDeviation(floorSupply, floorBalance) == 0`.
-/
def floorReserveRatioDeviationZero (s : ContractState) : Prop :=
  floorBalanceOf s = curveBalanceAt s (floorSupplyOf s)

def reserveRatioDeviationZero (s : ContractState) : Prop :=
  currentReserveRatioDeviationZero s ∧ floorReserveRatioDeviationZero s

def init_reserve_ratio_zero_spec (_s s' : ContractState) : Prop :=
  reserveRatioDeviationZero s'

def buy_preserves_reserve_ratio_zero_spec (s s' : ContractState) : Prop :=
  reserveRatioDeviationZero s -> reserveRatioDeviationZero s'

def sell_preserves_reserve_ratio_zero_spec (s s' : ContractState) : Prop :=
  reserveRatioDeviationZero s -> reserveRatioDeviationZero s'

def floorSellAndBurn_preserves_reserve_ratio_zero_spec (s s' : ContractState) : Prop :=
  reserveRatioDeviationZero s -> reserveRatioDeviationZero s'

end Benchmark.Cases.Polaris.BondingCurve
