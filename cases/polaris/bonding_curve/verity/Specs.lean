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

/-- Source helper: `virtualSupply() = floorSupply + totalSupply()`. -/
def virtualSupplyOf (s : ContractState) : Uint256 :=
  add (floorSupplyOf s) (totalSupplyOf s)

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

