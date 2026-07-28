import Verity.Specs.Common
import Benchmark.Cases.Starkware.StarkgateEscrow.Contract

namespace Benchmark.Cases.Starkware.StarkgateEscrow

open Verity
open Verity.EVM.Uint256

def assetBalanceOf (s : ContractState) : Uint256 := s.storage 0
def cumulativeDepositsOf (s : ContractState) : Uint256 := s.storage 1
def cumulativeWithdrawalsOf (s : ContractState) : Uint256 := s.storage 2

/--
Escrow lower-bound invariant: the L1 escrow balance is greater than or equal to
cumulative deposits minus cumulative withdrawals.

The inequality (not equality) preserves the donation caveat: the bridge balance
can exceed deposits minus withdrawals if tokens are sent directly to the contract
without going through `deposit`, or if ETH fees are credited.

Nat subtraction is used, so when cumulative withdrawals exceed cumulative
deposits the right-hand side is zero and the inequality holds trivially.
-/
def escrow_lower_bound_spec (s : ContractState) : Prop :=
  (assetBalanceOf s).val >= (cumulativeDepositsOf s).val - (cumulativeWithdrawalsOf s).val

def deposit_preserves_escrow_lower_bound_spec (s s' : ContractState) : Prop :=
  escrow_lower_bound_spec s -> escrow_lower_bound_spec s'

def withdraw_preserves_escrow_lower_bound_spec (s s' : ContractState) : Prop :=
  escrow_lower_bound_spec s -> escrow_lower_bound_spec s'

def depositReclaim_preserves_escrow_lower_bound_spec (s s' : ContractState) : Prop :=
  escrow_lower_bound_spec s -> escrow_lower_bound_spec s'

end Benchmark.Cases.Starkware.StarkgateEscrow
