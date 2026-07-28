import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Verity
open Verity.EVM.Uint256

private theorem address_ne_of_neq_zero {a : Address}
    (h : (a != zeroAddress) = true) : a ≠ (0 : Address) := by
  have hNe : a ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at h
  simpa [zeroAddress] using hNe

private theorem uint256_mod_uint64_of_lt {x : Uint256}
    (hx : x < UINT64_MOD) : x % 18446744073709551616 = x := by
  cases hBal : x with
  | mk val hlt =>
      have hval : val < 18446744073709551616 := by
        simpa [hBal, UINT64_MOD] using hx
      show (({ val := val, isLt := hlt } : Uint256) % 18446744073709551616) =
          ({ val := val, isLt := hlt } : Uint256)
      apply Verity.Core.Uint256.ext
      change (val % 18446744073709551616) % Verity.Core.Uint256.modulus = val
      rw [Nat.mod_eq_of_lt hval]
      exact Nat.mod_eq_of_lt hlt

/--
The exact-source `FHE.isInitialized(fromBalance)` guard fires before any write.
At the public wrapper, a passed wrapper predicate and valid nonzero addresses
therefore still produce `ERC7984ZeroBalance` with the original state.
-/
theorem uninitialized_sender_reverts_without_writes
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hUninitialized : s.storageMap 2 sender = 0) :
    uninitialized_sender_reverts_without_writes_spec
      ((ERC7984UpgradeableExact.confidentialTransfer
        sender recipient amount wrapperPreconditionsPassed).run s) s := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold uninitialized_sender_reverts_without_writes_spec
  simp [ERC7984UpgradeableExact.confidentialTransfer,
    ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
    ERC7984UpgradeableExact.balances,
    ERC7984UpgradeableExact.balanceInitialized,
    getMapping, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run,
    hWrapper, hSenderNZ, hRecipientNZ, hUninitialized]

/--
Once wrapper/plaintext guards pass and the sender handle is initialized, the
source's encrypted sufficiency result selects a transferred amount but cannot
select success versus revert.
-/
theorem initialized_transfer_no_balance_revert
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInitialized : balanceIsInitialized s sender) :
    initialized_transfer_no_balance_revert_spec
      ((ERC7984UpgradeableExact.confidentialTransfer
        sender recipient amount wrapperPreconditionsPassed).run s) := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold initialized_transfer_no_balance_revert_spec balanceIsInitialized at *
  simp [ERC7984UpgradeableExact.confidentialTransfer,
    ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
    ERC7984UpgradeableExact.balances,
    ERC7984UpgradeableExact.balanceInitialized,
    getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess,
    hWrapper, hSenderNZ, hRecipientNZ, hInitialized]

/--
For an initialized insufficient sender, the call succeeds with transferred = 0
and preserves the two plaintext-equivalent balances.
-/
theorem initialized_insufficient_transfer_zero
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInitialized : balanceIsInitialized s sender)
    (hDistinct : sender ≠ recipient)
    (hInsufficient : ¬ (balanceOf s sender >= amount))
    (hRecipient64 : balanceOf s recipient < UINT64_MOD) :
    initialized_insufficient_transfer_zero_spec sender recipient s
      ((ERC7984UpgradeableExact.confidentialTransfer
        sender recipient amount wrapperPreconditionsPassed).run s) := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
    simpa [balanceOf] using hInsufficient
  unfold initialized_insufficient_transfer_zero_spec balanceIsInitialized balanceOf at *
  constructor
  · simp [ERC7984UpgradeableExact.confidentialTransfer,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient']
  constructor
  · simp [ERC7984UpgradeableExact.confidentialTransfer,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.fst,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient']
  constructor
  · simp [ERC7984UpgradeableExact.confidentialTransfer,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient', hDistinct]
  · have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
    simp [ERC7984UpgradeableExact.confidentialTransfer,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient',
      hDistinct, hDistinct']
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd,
      Verity.Core.Uint256.add_zero]
    exact uint256_mod_uint64_of_lt hRecipient64

/--
Pairwise accounting conservation with every arithmetic/domain condition stated
explicitly. In particular, the theorem does not cover aliasing or uint64 wrap.
-/
theorem initialized_transfer_pair_conservation
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInitialized : balanceIsInitialized s sender)
    (hDistinct : sender ≠ recipient)
    (hRecipientNoWrap :
      balanceOf s recipient + selectedTransferAmount s sender amount < UINT64_MOD) :
    let s' := ((ERC7984UpgradeableExact.confidentialTransfer
      sender recipient amount wrapperPreconditionsPassed).run s).snd
    initialized_transfer_pair_conservation_spec sender recipient s s' := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold initialized_transfer_pair_conservation_spec balanceIsInitialized balanceOf at *
  by_cases hSufficient : s.storageMap 1 sender >= amount
  · dsimp
    have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
      simpa using hSufficient
    have hToNoWrap : s.storageMap 1 recipient + amount < UINT64_MOD := by
      simpa only [selectedTransferAmount, balanceOf, if_pos hSufficient]
        using hRecipientNoWrap
    simp [ERC7984UpgradeableExact.confidentialTransfer,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hSufficient',
      hDistinct, Ne.symm hDistinct]
    have hToAddMod : (s.storageMap 1 recipient + amount) % 18446744073709551616 =
        s.storageMap 1 recipient + amount :=
      uint256_mod_uint64_of_lt hToNoWrap
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [hToAddMod]
    calc
      sub (s.storageMap 1 sender) amount + (s.storageMap 1 recipient + amount)
          = (sub (s.storageMap 1 sender) amount + amount) + s.storageMap 1 recipient := by
              rw [Verity.Core.Uint256.add_comm (s.storageMap 1 recipient) amount]
              rw [← Verity.Core.Uint256.add_assoc]
      _ = s.storageMap 1 sender + s.storageMap 1 recipient := by
            change ((s.storageMap 1 sender - amount) + amount) + s.storageMap 1 recipient =
              s.storageMap 1 sender + s.storageMap 1 recipient
            rw [Verity.Core.Uint256.sub_add_cancel_left]
  · dsimp
    have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
      simpa using hSufficient
    have hToBal64 : s.storageMap 1 recipient < UINT64_MOD := by
      simpa only [selectedTransferAmount, balanceOf, if_neg hSufficient,
        Verity.Core.Uint256.add_zero] using hRecipientNoWrap
    simp [ERC7984UpgradeableExact.confidentialTransfer,
      ERC7984UpgradeableExact._transfer, ERC7984UpgradeableExact._update,
      ERC7984UpgradeableExact.balances,
      ERC7984UpgradeableExact.balanceInitialized,
      getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.snd,
      hWrapper, hSenderNZ, hRecipientNZ, hInitialized, hInsufficient',
      hDistinct, Ne.symm hDistinct, hToBal64]
    have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
        s.storageMap 1 recipient := by
      rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd,
        Verity.Core.Uint256.add_zero]
      exact uint256_mod_uint64_of_lt hToBal64
    rw [hZeroAddMod]

end Benchmark.Cases.Zama.ERC7984UpgradeableExactSource
