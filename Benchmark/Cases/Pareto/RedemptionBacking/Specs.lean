import Verity.Specs.Common
import Benchmark.Cases.Pareto.RedemptionBacking.Contract

namespace Benchmark.Cases.Pareto.RedemptionBacking

open Verity
open Verity.EVM.Uint256

def idleCollateralScaledOf (s : ContractState) : Uint256 := s.storage 0
def totCreditVaultsRequestedScaledOf (s : ContractState) : Uint256 := s.storage 1
def totReservedWithdrawalsOf (s : ContractState) : Uint256 := s.storage 2
def currentEpochPendingOf (s : ContractState) : Uint256 := s.storage 3
def previousEpochPendingOf (s : ContractState) : Uint256 := s.storage 4
def collateralizedFlagOf (s : ContractState) : Uint256 := s.storage 5

def idleCollateralScaled (s : ContractState) : Uint256 :=
  idleCollateralScaledOf s

def totCreditVaultsRequestedScaled (s : ContractState) : Uint256 :=
  totCreditVaultsRequestedScaledOf s

def closedClaims (s : ContractState) : Uint256 :=
  sub (totReservedWithdrawalsOf s) (currentEpochPendingOf s)

/--
Closed-epoch redemption reserve guard from `depositFunds`.

The current epoch is still open, so its `epochPending[epochNumber]` is excluded.
All burned USP from prior closed epochs remains covered by idle collateral plus
Credit Vault withdrawal value already requested but not yet claimed.
-/
def closed_epoch_reserve_guard (s : ContractState) : Prop :=
  (currentEpochPendingOf s).val <= (totReservedWithdrawalsOf s).val ∧
  (idleCollateralScaledOf s).val + (totCreditVaultsRequestedScaledOf s).val <
    Verity.Core.Uint256.modulus ∧
  (closedClaims s).val <=
    (add (idleCollateralScaledOf s) (totCreditVaultsRequestedScaledOf s)).val

def depositFunds_preserves_closed_epoch_reserve_guard_spec
    (_s s' : ContractState) : Prop :=
  closed_epoch_reserve_guard s'

def requestRedeem_preserves_closed_epoch_reserve_guard_spec
    (s s' : ContractState) : Prop :=
  closed_epoch_reserve_guard s -> closed_epoch_reserve_guard s'

end Benchmark.Cases.Pareto.RedemptionBacking
