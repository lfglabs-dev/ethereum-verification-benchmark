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
When the sender has insufficient balance, no tokens move.

If `balances[from] < amount`, then both balances are unchanged.
This is the defining semantic difference from ERC-20: insufficient
balance causes a silent 0-transfer (via FHE.select) instead of a revert.
-/
theorem transfer_insufficient
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hInsufficient : ¬(s.storageMap 1 sender >= amount))
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.transfer sender recipient amount).run s).snd
    transfer_insufficient_spec sender recipient amount s s' := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 sender).val := by
    simpa using hInsufficient
  unfold transfer_insufficient_spec balanceOf
  dsimp
  intro _
  constructor
  · simp [ERC7984.transfer, ERC7984._transfer, ERC7984._update, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit,
      hInsufficient', hToBal64]
    intro hEq
    exact False.elim (hDistinct hEq)
  · have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
    simp [ERC7984.transfer, ERC7984._transfer, ERC7984._update, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit, hInsufficient',
      hDistinct, hDistinct', hToBal64]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd, Verity.Core.Uint256.add_zero]
    exact uint256_mod_uint64_of_lt hToBal64
end Benchmark.Cases.Zama.ERC7984ConfidentialToken
