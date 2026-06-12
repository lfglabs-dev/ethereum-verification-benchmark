import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
Operator-gated transferFrom preserves balance conservation.

When the caller is authorized (either `holder == msg.sender` or
`block.timestamp <= operators[holder][msg.sender]`), transferFrom
preserves the sum `balances[holder] + balances[recipient]`.

This ensures that delegating transfer authority via the operator
pattern does not allow creation or destruction of tokens.
-/
theorem transferFrom_conservation
    (holder recipient : Address) (amount blockTimestamp : Uint256)
    (s : ContractState)
    (hFrom : (holder != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 holder ≠ 0)
    (hDistinct : holder ≠ recipient)
    (hAuthorized :
      holder == s.sender ∨ blockTimestamp <= s.storageMap2 3 holder s.sender)
    (hAmount64 : amount < UINT64_MOD)
    (hHolderBal64 : s.storageMap 1 holder < UINT64_MOD)
    (hRecipientBal64 : s.storageMap 1 recipient < UINT64_MOD)
    (hToNoWrap : s.storageMap 1 recipient + amount < UINT64_MOD) :
    let s' := ((ERC7984.transferFrom holder recipient amount blockTimestamp).run s).snd
    transferFrom_conservation_spec holder recipient s s' := by
  have hHolderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  have hAuthorized' : holder = s.sender ∨ blockTimestamp.val ≤ (s.storageMap2 3 holder s.sender).val := by
    cases hAuthorized with
    | inl hEq =>
        exact Or.inl ((beq_iff_eq).1 hEq)
    | inr hLe =>
        exact Or.inr (by simpa using hLe)
  unfold transferFrom_conservation_spec balanceOf
  by_cases hSufficient : s.storageMap 1 holder >= amount
  · dsimp
    have hSufficient' : amount.val ≤ (s.storageMap 1 holder).val := by
      simpa using hSufficient
    simp [ERC7984.transferFrom, ERC7984._transfer, ERC7984._update, ERC7984.operators, ERC7984.balances,
      ERC7984.balanceInitialized, add64, UINT64_MOD, getMapping2, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      msgSender, Contract.run, ContractResult.snd, hHolderNZ, hRecipientNZ, hInit,
      hSufficient', hDistinct, Ne.symm hDistinct, hAuthorized']
    have hToAddMod : (s.storageMap 1 recipient + amount) % 18446744073709551616 =
        s.storageMap 1 recipient + amount :=
      uint256_mod_uint64_of_lt hToNoWrap
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd]
    rw [hToAddMod]
    calc
      sub (s.storageMap 1 holder) amount + (s.storageMap 1 recipient + amount)
          = (sub (s.storageMap 1 holder) amount + amount) + s.storageMap 1 recipient := by
              rw [Verity.Core.Uint256.add_comm (s.storageMap 1 recipient) amount]
              rw [← Verity.Core.Uint256.add_assoc]
      _ = s.storageMap 1 holder + s.storageMap 1 recipient := by
            change ((s.storageMap 1 holder - amount) + amount) + s.storageMap 1 recipient =
              s.storageMap 1 holder + s.storageMap 1 recipient
            rw [Verity.Core.Uint256.sub_add_cancel_left]
  · dsimp
    have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 holder).val := by
      simpa using hSufficient
    simp [ERC7984.transferFrom, ERC7984._transfer, ERC7984._update, ERC7984.operators, ERC7984.balances,
      ERC7984.balanceInitialized, add64, UINT64_MOD, getMapping2, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      msgSender, Contract.run, ContractResult.snd, hHolderNZ, hRecipientNZ, hInit,
      hInsufficient', hDistinct, Ne.symm hDistinct, hAuthorized', hRecipientBal64]
    have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
        s.storageMap 1 recipient := by
      rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd, Verity.Core.Uint256.add_zero]
      exact uint256_mod_uint64_of_lt hRecipientBal64
    rw [hZeroAddMod]
end Benchmark.Cases.Zama.ERC7984ConfidentialToken
