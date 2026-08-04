import Verity.Specs.Common
import Benchmark.Cases.Velora.BridgeStaking.Contract

namespace Benchmark.Cases.Velora.BridgeStaking

open Verity
open Verity.EVM.Uint256

/-!
  Specifications for the Velora BridgeStaking `allocatedTokens` conservation
  invariant. Every Solidity-checked addition and subtraction is represented in
  `Contract.lean` by `addPanic` or `subPanic`. Arithmetic failure therefore
  reverts, and `Contract.run` returns the original state. The withdrawal and
  rescue theorems cover all successful and reverting paths from conservation
  alone, including explicit failed SafeTransferLib results.

  Relating the modeled balance slots to Solidity assumes that entry balances
  already include the Across delivery, `balanceOf(address(this))` is faithful,
  successful standard ERC-20 transfers debit exactly the requested amount, and
  no fees, rebases, seizures, donations, or other token-balance changes occur
  during the atomic call. `depositResult` and the Boolean transfer-result inputs
  are unconstrained results of narrow external-call boundaries; false transfer
  results revert the whole modeled call to its incoming state.

  Flattened semantic storage (not the upstream EVM storage layout):
    slot 0: vlrBalance; slot 1: wethBalance
    slot 2: allocatedVLR; slot 3: allocatedWETH
    slot 4: stakingVlrAmount[key]; slot 5: stakingWethAmount[key]
    slot 6: stakingBeneficiary[key]
    slot 7: stakingVlrReceived[key]; slot 8: stakingWethReceived[key]
-/

/-! ## Storage accessors and invariant -/

def vlrBalanceOf (s : ContractState) : Uint256 := s.storage 0
def wethBalanceOf (s : ContractState) : Uint256 := s.storage 1
def allocatedVLROf (s : ContractState) : Uint256 := s.storage 2
def allocatedWETHOf (s : ContractState) : Uint256 := s.storage 3

/-- VLR conservation: allocated VLR does not exceed the held VLR balance. -/
def allocatedVlrInvariant (s : ContractState) : Prop :=
  (allocatedVLROf s).val <= (vlrBalanceOf s).val

/-- WETH conservation: allocated WETH does not exceed the held WETH balance. -/
def allocatedWethInvariant (s : ContractState) : Prop :=
  (allocatedWETHOf s).val <= (wethBalanceOf s).val

/-- Combined conservation invariant for both tokens. -/
def allocatedConservationInvariant (s : ContractState) : Prop :=
  allocatedVlrInvariant s ∧ allocatedWethInvariant s

/-! ## Per-function preservation specs -/

/--
Handle-message preservation for the actual modeled transition, including new-record
initialization, existing-record stored-amount validation, and every arithmetic or
explicit-guard revert.
-/
def handleV3AcrossMessage_preserves_spec
    (key vlrAmount wethAmount minBptAmount : Uint256)
    (beneficiary : Address)
    (isVlr : Bool)
    (receivedAmount depositResult : Uint256)
    (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState) : Prop :=
  let s' := ((Staking.handleV3AcrossMessage
    key vlrAmount wethAmount minBptAmount beneficiary isVlr receivedAmount
      depositResult vlrTransferSuccess wethTransferSuccess).run s).snd
  allocatedConservationInvariant s → allocatedConservationInvariant s'

/--
Rescue preservation for the actual run-derived post-state. This covers every
receipt-flag combination, explicit guard failure, checked underflow, and transfer
result from the incoming conservation invariant alone.
-/
def rescuePendingFunds_preserves_spec (key : Uint256)
    (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState) : Prop :=
  let s' := ((Staking.rescuePendingFunds key vlrTransferSuccess
    wethTransferSuccess).run s).snd
  allocatedConservationInvariant s →
  allocatedConservationInvariant s'

/-- Withdrawal preservation, including arithmetic, zero-amount, and transfer reverts. -/
def withdrawUnallocatedTokens_preserves_spec (isVlr transferSuccess : Bool)
    (s : ContractState) : Prop :=
  let s' := ((Staking.withdrawUnallocatedTokens isVlr transferSuccess).run s).snd
  allocatedConservationInvariant s → allocatedConservationInvariant s'

end Benchmark.Cases.Velora.BridgeStaking
