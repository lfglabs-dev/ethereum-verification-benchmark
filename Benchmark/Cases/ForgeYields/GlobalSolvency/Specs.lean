import Verity.Specs.Common
import Benchmark.Cases.ForgeYields.GlobalSolvency.Contract

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

def assetBalanceOf (s : ContractState) : Uint256 := s.storage 0
def bufferOf (s : ContractState) : Uint256 := s.storage 1
def assetsLockedOf (s : ContractState) : Uint256 := s.storage 2
def depreciatedOf (s : ContractState) : Uint256 := s.storage 3

/-- While the gateway is active, ERC20 balance covers buffer plus locked redeem assets. -/
def global_solvency_spec (s : ContractState) : Prop :=
  depreciatedOf s != 0 ∨ (bufferOf s).val + (assetsLockedOf s).val <= (assetBalanceOf s).val

def deposit_preserves_global_solvency_spec (s s' : ContractState) : Prop :=
  global_solvency_spec s -> global_solvency_spec s'

def requestRedeem_preserves_global_solvency_spec (s s' : ContractState) : Prop :=
  global_solvency_spec s -> global_solvency_spec s'

def claimRedeem_preserves_global_solvency_spec (s s' : ContractState) : Prop :=
  global_solvency_spec s -> global_solvency_spec s'

def redeemTokenGatewayDepreciated_preserves_global_solvency_spec (s s' : ContractState) : Prop :=
  global_solvency_spec s -> global_solvency_spec s'

def transferRemote_preserves_global_solvency_spec (s s' : ContractState) : Prop :=
  global_solvency_spec s -> global_solvency_spec s'

def handle_preserves_global_solvency_spec (s s' : ContractState) : Prop :=
  global_solvency_spec s -> global_solvency_spec s'

def report_preserves_global_solvency_spec (s s' : ContractState) : Prop :=
  global_solvency_spec s -> global_solvency_spec s'

end Benchmark.Cases.ForgeYields.GlobalSolvency
