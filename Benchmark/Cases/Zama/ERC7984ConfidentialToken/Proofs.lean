import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity
open Verity.EVM.Uint256

/-
  Reference proofs for the Zama / OpenZeppelin ERC-7984 confidential token.

  This module contains only fully proven theorems (no placeholders).

  Structure:
    Part 0 — Shared utilities (address non-zero conversion, mod 2^64 identity)
    Part 1 — transfer (conservation, sufficient, insufficient, preserves_supply,
                       no_balance_revert)
    Part 2 — mint (increases_supply, overflow_protection)
    Part 3 — burn (decreases_supply)
-/

/-! ═══════════════════════════════════════════════════════════════════
    Part 0: Shared utilities
    ═══════════════════════════════════════════════════════════════════ -/

/-- Convert an `!= zeroAddress` Bool fact into a Lean `≠ (0 : Address)` fact. -/
private theorem address_ne_of_neq_zero {a : Address}
    (h : (a != zeroAddress) = true) : a ≠ (0 : Address) := by
  have hNe : a ≠ zeroAddress := by
    intro hEq
    subst hEq
    simp at h
  simpa [zeroAddress] using hNe

/-- For a `Uint256` value that fits in `[0, 2^64)`, taking `% 2^64` is the identity. -/
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

/-! ═══════════════════════════════════════════════════════════════════
    Part 1: transfer
    ═══════════════════════════════════════════════════════════════════ -/

/--
Transfer conserves the sum of sender and receiver balances.

After transfer(from, to, amount), `balances[from] + balances[to]` is unchanged.
This holds regardless of whether the sender has sufficient balance:
- Sufficient: from loses `amount`, to gains `amount` → sum preserved
- Insufficient: both balances unchanged → sum trivially preserved
-/
theorem transfer_conservation
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD)
    (hToNoWrap : s.storageMap 1 recipient + amount < UINT64_MOD) :
    let s' := ((ERC7984.transfer sender recipient amount).run s).snd
    transfer_conservation_spec sender recipient s s' := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold transfer_conservation_spec balanceOf
  by_cases hSufficient : s.storageMap 1 sender >= amount
  · dsimp
    have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
      simpa using hSufficient
    simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit, hSufficient',
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
    simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit, hInsufficient',
      hDistinct, Ne.symm hDistinct, hToBal64]
    have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
        s.storageMap 1 recipient := by
      rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd, Verity.Core.Uint256.add_zero]
      exact uint256_mod_uint64_of_lt hToBal64
    rw [hZeroAddMod]

/--
When the sender has sufficient balance, transfer moves exactly `amount` tokens.

If `balances[from] >= amount`, then:
- `balances[from]` decreases by `amount`
- `balances[to]` increases by `amount` (mod 2^64)
-/
theorem transfer_sufficient
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hSufficient : s.storageMap 1 sender >= amount)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.transfer sender recipient amount).run s).snd
    transfer_sufficient_spec sender recipient amount s s' := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  have hSufficient' : amount.val ≤ (s.storageMap 1 sender).val := by
    simpa using hSufficient
  unfold transfer_sufficient_spec balanceOf
  dsimp
  intro _
  constructor
  · simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit,
      hSufficient', hDistinct]
  · have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
    simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit,
      hSufficient', hDistinct, hDistinct']

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
  · simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit,
      hInsufficient', hToBal64]
    intro hEq
    exact False.elim (hDistinct hEq)
  · have hDistinct' : recipient ≠ sender := Ne.symm hDistinct
    simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
      add64, UINT64_MOD, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit, hInsufficient',
      hDistinct, hDistinct', hToBal64]
    rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd, Verity.Core.Uint256.add_zero]
    exact uint256_mod_uint64_of_lt hToBal64

/--
Transfer does not modify totalSupply.

The transfer function only writes to balances (storageMap slot 1) and
balanceInitialized (storageMap slot 2). It never touches slot 0 (totalSupply).
Only mint and burn paths modify totalSupply.
-/
theorem transfer_preserves_supply
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.transfer sender recipient amount).run s).snd
    transfer_preserves_supply_spec s s' := by
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold transfer_preserves_supply_spec supply
  simp [ERC7984.transfer, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
    add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
    Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
    Contract.run, ContractResult.snd, hSenderNZ, hRecipientNZ, hInit]

/--
Transfer never reverts based on balance sufficiency.

Given that all plaintext preconditions hold (non-zero addresses,
initialized sender balance), the transfer always succeeds — it
returns `ContractResult.success`, never `ContractResult.revert`.

This is the contract-level non-leakage invariant for ERC-7984:
an on-chain observer cannot learn whether the sender had sufficient
balance by checking if the transaction reverted. The only reverts
come from plaintext checks (zero address, uninitialized balance).

Note: NO hypothesis about `fromBalance >= amount` is provided.
The theorem must hold for BOTH sufficient and insufficient balances.
-/
theorem transfer_no_balance_revert
    (sender recipient : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInit : s.storageMap 2 sender ≠ 0)
    (hDistinct : sender ≠ recipient)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 sender < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    transfer_no_balance_revert_spec sender recipient amount s := by
  let _ := hDistinct
  let _ := hAmount64
  let _ := hFromBal64
  let _ := hToBal64
  have hSenderNZ := address_ne_of_neq_zero hFrom
  have hRecipientNZ := address_ne_of_neq_zero hTo
  unfold transfer_no_balance_revert_spec
  simp [ERC7984.transfer, ERC7984.balances, ERC7984.balanceInitialized,
    getMapping, setMapping, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure, Contract.run, ContractResult.isSuccess,
    hSenderNZ, hRecipientNZ, hInit]

/-! ═══════════════════════════════════════════════════════════════════
    Part 2: mint
    ═══════════════════════════════════════════════════════════════════ -/

/--
Successful mint increases totalSupply and receiver balance by amount.

When totalSupply + amount does not overflow uint64 (tryIncrease64 succeeds),
minting produces exactly `amount` new tokens: totalSupply increases by amount
and balances[to] increases by amount (mod 2^64).
-/
theorem mint_increases_supply
    (recipient : Address) (amount : Uint256) (s : ContractState)
    (hTo : (recipient != zeroAddress) = true)
    (hNoOverflow : (tryIncrease64 (s.storage 0) amount).1 = true)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.mint recipient amount).run s).snd
    mint_increases_supply_spec recipient amount s s' := by
  have hRecipientNZ := address_ne_of_neq_zero hTo
  have hSuccess : add64 (s.storage 0) amount >= s.storage 0 := by
    by_cases h : add64 (s.storage 0) amount >= s.storage 0
    · exact h
    · unfold tryIncrease64 at hNoOverflow
      simp [h] at hNoOverflow
  have hSuccess' : (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
    simpa [add64, UINT64_MOD] using hSuccess
  unfold mint_increases_supply_spec supply balanceOf
  dsimp
  intro _
  constructor
  · simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hSuccess']
  · simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hSuccess']

/--
Mint overflow protection: when totalSupply + amount overflows uint64,
no tokens are minted.

FHESafeMath.tryIncrease detects overflow by checking whether
(oldValue + delta) mod 2^64 >= oldValue. On overflow, the wrapped sum
is less than oldValue, so tryIncrease returns (false, oldValue).
Then FHE.select picks 0 as the transferred amount.
-/
theorem mint_overflow_protection
    (recipient : Address) (amount : Uint256) (s : ContractState)
    (hTo : (recipient != zeroAddress) = true)
    (hOverflow : (tryIncrease64 (s.storage 0) amount).1 = false)
    (hAmount64 : amount < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD)
    (hToBal64 : s.storageMap 1 recipient < UINT64_MOD) :
    let s' := ((ERC7984.mint recipient amount).run s).snd
    mint_overflow_protection_spec recipient amount s s' := by
  have hRecipientNZ := address_ne_of_neq_zero hTo
  have hFail : ¬ add64 (s.storage 0) amount >= s.storage 0 := by
    intro hSuccess
    have : (tryIncrease64 (s.storage 0) amount).1 = true := by
      simp [tryIncrease64, hSuccess]
    rw [this] at hOverflow
    contradiction
  have hFail' : ¬ (s.storage 0).val ≤ (add (s.storage 0) amount % 18446744073709551616).val := by
    simpa [add64, UINT64_MOD] using hFail
  unfold mint_overflow_protection_spec supply balanceOf
  dsimp
  intro _
  constructor
  · simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hFail', hToBal64]
  · simp [ERC7984.mint, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      tryIncrease64, add64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hRecipientNZ, hFail', hToBal64]

/-! ═══════════════════════════════════════════════════════════════════
    Part 3: burn
    ═══════════════════════════════════════════════════════════════════ -/

/--
Successful burn decreases both sender balance and totalSupply.

When the sender has sufficient balance (fromBalance >= amount), burning
decreases balances[from] by amount and totalSupply by amount.
-/
theorem burn_decreases_supply
    (holder : Address) (amount : Uint256) (s : ContractState)
    (hFrom : (holder != zeroAddress) = true)
    (hInit : s.storageMap 2 holder ≠ 0)
    (hSufficient : s.storageMap 1 holder >= amount)
    (hAmount64 : amount < UINT64_MOD)
    (hFromBal64 : s.storageMap 1 holder < UINT64_MOD)
    (hSupply64 : s.storage 0 < UINT64_MOD) :
    let s' := ((ERC7984.burn holder amount).run s).snd
    burn_decreases_supply_spec holder amount s s' := by
  have hHolderNZ := address_ne_of_neq_zero hFrom
  have hSufficient' : amount.val ≤ (s.storageMap 1 holder).val := by
    simpa using hSufficient
  unfold burn_decreases_supply_spec balanceOf supply
  dsimp
  intro _
  constructor
  · simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hHolderNZ, hInit, hSufficient']
  · simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hHolderNZ, hInit, hSufficient']

/--
When the holder has insufficient balance, burn silently burns nothing.

If `balances[holder] < amount`, then both the holder balance and totalSupply
remain unchanged.
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
  · simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hHolderNZ, hInit, hInsufficient']
  · simp [ERC7984.burn, ERC7984.totalSupply, ERC7984.balances, ERC7984.balanceInitialized,
      add64, sub64, UINT64_MOD, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd, hHolderNZ, hInit, hInsufficient', hSupply64]
    change (s.storage 0 - 0) % 18446744073709551616 = s.storage 0
    rw [Verity.Core.Uint256.sub_zero]
    exact uint256_mod_uint64_of_lt hSupply64

/-! ═══════════════════════════════════════════════════════════════════
    Part 4: transferFrom
    ═══════════════════════════════════════════════════════════════════ -/

/--
Authorized transferFrom conserves the sum of holder and recipient balances.

When the operator authorization check passes, `transferFrom` follows the same
accounting path as `transfer`, so `balances[holder] + balances[recipient]`
is preserved.
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
    simp [ERC7984.transferFrom, ERC7984.operators, ERC7984.balances,
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
    simp [ERC7984.transferFrom, ERC7984.operators, ERC7984.balances,
      ERC7984.balanceInitialized, add64, UINT64_MOD, getMapping2, getMapping,
      setMapping, Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      msgSender, Contract.run, ContractResult.snd, hHolderNZ, hRecipientNZ, hInit,
      hInsufficient', hDistinct, Ne.symm hDistinct, hAuthorized', hRecipientBal64]
    have hZeroAddMod : add (s.storageMap 1 recipient) 0 % 18446744073709551616 =
        s.storageMap 1 recipient := by
      rw [Verity.Proofs.Stdlib.Automation.evm_add_eq_hadd, Verity.Core.Uint256.add_zero]
      exact uint256_mod_uint64_of_lt hRecipientBal64
    rw [hZeroAddMod]

/-! ═══════════════════════════════════════════════════════════════════
    Part 5: setOperator
    ═══════════════════════════════════════════════════════════════════ -/

/--
setOperator writes the caller/operator expiry pair and leaves all other
operator entries unchanged.
-/
theorem setOperator_updates
    (operator : Address) (expiry : Uint256) (s : ContractState) :
    let s' := ((ERC7984.setOperator operator expiry).run s).snd
    setOperator_updates_spec s.sender operator expiry s s' := by
  unfold setOperator_updates_spec operatorExpiry ERC7984.setOperator
  dsimp
  constructor
  · simp [ERC7984.operators, setMapping2, msgSender, Contract.run, ContractResult.snd,
      Verity.bind, Bind.bind, Verity.pure, Pure.pure]
  · intro h sp hNe
    by_cases hHolder : h = s.sender
    · subst h
      have hSpNe : sp ≠ operator := by
        intro hSpEq
        apply hNe
        cases hSpEq
        rfl
      simp [ERC7984.operators, setMapping2, msgSender, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, hSpNe]
    · simp [ERC7984.operators, setMapping2, msgSender, Contract.run, ContractResult.snd,
        Verity.bind, Bind.bind, Verity.pure, Pure.pure, hHolder]

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
