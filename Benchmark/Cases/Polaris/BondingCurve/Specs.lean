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

/--
  Helper-output policy: the executable model receives the Solidity
  `_getBalanceFromReserveRatio` result as an input because this benchmark does
  not model PRB/ABDK fixed-point exponentiation bit-for-bit. The predicate
  states the exact proof obligation for such an input: it must equal the
  benchmark's rounded reserve abstraction at the same supply.
-/
def trustedCurveHelperOutput (supply reserve : Uint256) : Prop :=
  reserve = curveBalance supply

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
  The model names the rounded reserve function directly as `curveBalance`.
-/
def currentReserveRatioDeviationZero (s : ContractState) : Prop :=
  virtualBalanceOf s = curveBalance (virtualSupplyOf s)

/--
  Readable form of `reserveRatioDeviation(floorSupply, floorBalance) == 0`.
-/
def floorReserveRatioDeviationZero (s : ContractState) : Prop :=
  floorBalanceOf s = curveBalance (floorSupplyOf s)

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
