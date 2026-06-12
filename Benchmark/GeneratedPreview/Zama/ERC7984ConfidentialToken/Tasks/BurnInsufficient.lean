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
When the holder has insufficient balance, burn silently burns nothing.

If `balances[holder] < amount`, then both the holder's balance and
totalSupply are unchanged. This mirrors the FHE.select pattern used
in transfer: the balance comparison cannot cause a revert or leak
information; it only chooses between transferring `amount` and `0`.
-/
theorem burn_insufficient
    (holder : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (holder != zeroAddress) = true)
    (hInit : s.storageMap 2 holder ≠ 0)
    (hInsufficient : ¬(s.storageMap 1 holder >= amount))
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 holder < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD) :
    let s' := ((ERC7984.burn holder amount).run s).snd
    burn_insufficient_spec holder amount s s' := by
  have hHolderNZ := address_ne_of_neq_zero hFrom
  have hInsufficient' : ¬ amount.val ≤ (s.storageMap 1 holder).val := by
    simpa using hInsufficient
  unfold burn_insufficient_spec balanceOf supply
  dsimp
  intro _
  constructor
  · simp [ERC7984.burn, ERC7984._burn, ERC7984._update, ERC7984.totalSupply, ERC7984.totalSupplyInitialized, ERC7984.balances, ERC7984.balanceInitialized,
      add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hHolderNZ, hInit, hInsufficient']
  · simp [ERC7984.burn, ERC7984._burn, ERC7984._update, ERC7984.totalSupply, ERC7984.totalSupplyInitialized, ERC7984.balances, ERC7984.balanceInitialized,
      add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hHolderNZ, hInit, hInsufficient', hSupply64]
    change (s.storage 0 - 0) % 18446744073709551616 = s.storage 0
    rw [Verity.Core.Uint256.sub_zero]
    exact uint256_mod_uint64_of_lt hSupply64
end Benchmark.Cases.Zama.ERC7984ConfidentialToken
