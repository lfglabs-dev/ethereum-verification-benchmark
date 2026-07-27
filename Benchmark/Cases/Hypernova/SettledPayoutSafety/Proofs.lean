import Benchmark.Cases.Hypernova.SettledPayoutSafety.Specs
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.Math

namespace Benchmark.Cases.Hypernova.SettledPayoutSafety

open Verity
open Verity.EVM.Uint256

set_option linter.unusedSimpArgs false

/-- Distinct struct word offsets remain distinct modulo the EVM storage modulus. -/
private theorem structSlot2_offset_ne
    (baseSlot key1 key2 offset1 offset2 : Nat)
    (hOffsetNe : offset1 ≠ offset2)
    (hOffset1 : offset1 < Compiler.Constants.evmModulus)
    (hOffset2 : offset2 < Compiler.Constants.evmModulus) :
    Contracts.structSlot2 baseSlot key1 key2 offset1 ≠
      Contracts.structSlot2 baseSlot key1 key2 offset2 := by
  intro hEq
  let nestedBase :=
    Compiler.Proofs.abstractMappingSlot
      (Compiler.Proofs.abstractMappingSlot baseSlot key1) key2
  have hMod :
      nestedBase + offset1 ≡ nestedBase + offset2
        [MOD Compiler.Constants.evmModulus] := by
    simpa [Contracts.structSlot2, nestedBase] using hEq
  have hOffsets :
      offset1 ≡ offset2 [MOD Compiler.Constants.evmModulus] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl nestedBase) hMod
  exact hOffsetNe (hOffsets.eq_of_lt_of_lt hOffset1 hOffset2)

@[simp] private theorem storageWordUint256_roundtrip (word : Uint256) :
    (Contracts.StorageWord.fromWord
      (Contracts.StorageWord.toWord word) : Uint256) = word :=
  rfl

private theorem div_val_of_ne_zero (a b : Uint256) (hb : b.val ≠ 0)
    (hDivLt : a.val / b.val < modulus) :
    (div a b).val = a.val / b.val := by
  show (Verity.Core.Uint256.div a b).val = a.val / b.val
  unfold Verity.Core.Uint256.div
  rw [if_neg hb]
  show (Verity.Core.Uint256.ofNat (a.val / b.val)).val = a.val / b.val
  rw [Verity.Core.Uint256.val_ofNat]
  exact Nat.mod_eq_of_lt hDivLt

private theorem bpsDenominator_val : BPS_DENOMINATOR.val = 10000 := by
  native_decide

/-- The clamped basis-point formula never exceeds its gross input, even after
`Uint256` modular multiplication. Successful source execution is therefore not needed
for this arithmetic bound. -/
private theorem traderPayoutAmount_le_amount
    (s : ContractState) (trader : Address) (amount : Uint256) :
    traderPayoutAmount s trader amount <= amount := by
  let split := effectiveTraderSplit
    (s.storageMap 12 HypernovaPayoutSystem.pinnedVault)
    (s.storageMap 5 trader)
  have hSplitLe : split.val ≤ 10000 := by
    dsimp [split, effectiveTraderSplit]
    simp only [Verity.Core.Uint256.val_ite, Verity.Core.Uint256.lt_def,
      bpsDenominator_val]
    by_cases h :
        10000 < (add (s.storageMap 12 HypernovaPayoutSystem.pinnedVault)
          (s.storageMap 5 trader)).val
    · simp [h]
    · simp [h, Nat.le_of_not_gt h]
  have hBpsNe : BPS_DENOMINATOR.val ≠ 0 := by
    rw [bpsDenominator_val]
    decide
  have hDivLt :
      (mul amount split).val / BPS_DENOMINATOR.val < modulus :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (mul amount split).isLt
  have hDivVal :
      (div (mul amount split) BPS_DENOMINATOR).val =
        (mul amount split).val / BPS_DENOMINATOR.val :=
    div_val_of_ne_zero _ _ hBpsNe hDivLt
  have hMulVal :
      (mul amount split).val =
        (amount.val * split.val) % modulus := by
    rfl
  change (div (mul amount split) BPS_DENOMINATOR).val ≤ amount.val
  rw [hDivVal, hMulVal, bpsDenominator_val]
  calc
    (amount.val * split.val) % modulus / 10000 ≤
        (amount.val * split.val) / 10000 :=
      Nat.div_le_div_right (Nat.mod_le _ _)
    _ ≤ (amount.val * 10000) / 10000 :=
      Nat.div_le_div_right (Nat.mul_le_mul_left amount.val hSplitLe)
    _ = amount.val := Nat.mul_div_cancel _ (by decide)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- A valid settled payout request preserves the requested accounting guarantees. -/
theorem validSettledPayout_is_safe
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool)
    (hValid : validSettledPayoutRequest s trader fundedAccountId amount deadline v r signatureS transferSucceeds) :
    settledPayoutSafety s trader fundedAccountId amount deadline v r signatureS transferSucceeds := by
  rcases hValid with
    ⟨hExists, hSuspended, hDeadline, hAmount, hVault, hStatusActive,
      hCanWithdraw, hEquity, hAmountLeProfit, hSigner, hTotalBalance,
      hTraderNonzero, hAmountAllocated, hSplitAdd, hSplitMul,
      hTraderAmountBalance, hNonceAdd, hTraderAdd, hTransfer⟩
  rcases hVault with ⟨hConfiguredVault, hVaultImmutable, hDomain, hDistinct⟩
  have hPinnedVaultNonzero : HypernovaPayoutSystem.pinnedVault ≠ zeroAddress := by
    native_decide
  have hConfiguredNonzero : s.storageAddr 0 ≠ zeroAddress := by
    rw [hConfiguredVault]
    exact hPinnedVaultNonzero
  have hVaultImmutableLiteral :
      s.storageAddr 15 = HypernovaPayoutSystem.pinnedTradingAccounts := by
    simpa [HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts] using
      hVaultImmutable
  have hStatusExists : fundedStatusAt s trader fundedAccountId ≠ 0 := by
    rw [hStatusActive]
    native_decide
  have hActiveNonzeroLiteral : (2 : Uint256) ≠ 0 := by
    native_decide
  have hProfitSub := Verity.Proofs.Stdlib.Math.safeSub_some
    (equityAt s trader fundedAccountId) (initialEquityAt s trader fundedAccountId)
    (Nat.le_of_lt hEquity)
  have hProfitLeEquity := Verity.Proofs.Stdlib.Math.safeSub_result_le
    (equityAt s trader fundedAccountId) (initialEquityAt s trader fundedAccountId)
    (settledProfit s trader fundedAccountId) hProfitSub
  have hProfitLeEquityVal :
      (settledProfit s trader fundedAccountId).val <=
        (equityAt s trader fundedAccountId).val := by
    exact hProfitLeEquity
  have hAmountLeEquity : amount.val <= (equityAt s trader fundedAccountId).val :=
    Nat.le_trans hAmountLeProfit hProfitLeEquityVal
  have hEquitySub := Verity.Proofs.Stdlib.Math.safeSub_some
    (equityAt s trader fundedAccountId) amount hAmountLeEquity
  have hVaultSub := Verity.Proofs.Stdlib.Math.safeSub_some
    (s.storageMap 13 HypernovaPayoutSystem.pinnedVault)
    (traderPayoutAmount s trader amount) hTraderAmountBalance
  have hTraderLeAmount := traderPayoutAmount_le_amount s trader amount
  have hProtocolSub := Verity.Proofs.Stdlib.Math.safeSub_some
    amount (traderPayoutAmount s trader amount) hTraderLeAmount
  have hAmountAllocatedVal :
      amount.val <=
        (s.storageMap 11 HypernovaPayoutSystem.pinnedVault).val :=
    hAmountAllocated
  let traderKey := Contracts.StorageKey.toWord trader
  let accountKey := Contracts.StorageKey.toWord fundedAccountId
  have hSlot0Ne3 :
      Contracts.structSlot2 3 traderKey accountKey 0 ≠
        Contracts.structSlot2 3 traderKey accountKey 3 := by
    apply structSlot2_offset_ne
    all_goals norm_num [Compiler.Constants.evmModulus]
  have hSlot0Ne4 :
      Contracts.structSlot2 3 traderKey accountKey 0 ≠
        Contracts.structSlot2 3 traderKey accountKey 4 := by
    apply structSlot2_offset_ne
    all_goals norm_num [Compiler.Constants.evmModulus]
  have hSlot1Ne3 :
      Contracts.structSlot2 3 traderKey accountKey 1 ≠
        Contracts.structSlot2 3 traderKey accountKey 3 := by
    apply structSlot2_offset_ne
    all_goals norm_num [Compiler.Constants.evmModulus]
  have hSlot1Ne4 :
      Contracts.structSlot2 3 traderKey accountKey 1 ≠
        Contracts.structSlot2 3 traderKey accountKey 4 := by
    apply structSlot2_offset_ne
    all_goals norm_num [Compiler.Constants.evmModulus]
  have hSlot3Ne4 :
      Contracts.structSlot2 3 traderKey accountKey 3 ≠
        Contracts.structSlot2 3 traderKey accountKey 4 := by
    apply structSlot2_offset_ne
    all_goals norm_num [Compiler.Constants.evmModulus]
  have hSlot4Ne3 :
      Contracts.structSlot2 3 traderKey accountKey 4 ≠
        Contracts.structSlot2 3 traderKey accountKey 3 := by
    exact Ne.symm hSlot3Ne4
  have hPostEquityGeInitial :
      sub (equityAt s trader fundedAccountId) amount >=
        initialEquityAt s trader fundedAccountId := by
    simp only [Verity.Core.Uint256.le_def]
    have hPostSubVal :
        (sub (equityAt s trader fundedAccountId) amount).val =
          (equityAt s trader fundedAccountId).val - amount.val := by
      change
        (((equityAt s trader fundedAccountId) - amount : Uint256) : Nat) =
          (equityAt s trader fundedAccountId).val - amount.val
      exact Verity.Core.Uint256.sub_eq_of_le hAmountLeEquity
    rw [hPostSubVal]
    have hProfitVal :
        (settledProfit s trader fundedAccountId).val =
          (equityAt s trader fundedAccountId).val -
            (initialEquityAt s trader fundedAccountId).val := by
      unfold settledProfit
      exact Verity.Core.Uint256.sub_eq_of_le (Nat.le_of_lt hEquity)
    have hAmountLeProfitVal :
        amount.val <=
          (equityAt s trader fundedAccountId).val -
            (initialEquityAt s trader fundedAccountId).val := by
      calc
        amount.val <= (settledProfit s trader fundedAccountId).val := hAmountLeProfit
        _ = (equityAt s trader fundedAccountId).val -
            (initialEquityAt s trader fundedAccountId).val := hProfitVal
    have hAmountPlusInitialLeEquity :
        amount.val + (initialEquityAt s trader fundedAccountId).val <=
          (equityAt s trader fundedAccountId).val :=
      Nat.add_le_of_le_sub (Nat.le_of_lt hEquity) hAmountLeProfitVal
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using hAmountPlusInitialLeEquity
  have hOneSubOne : sub (1 : Uint256) 1 = 0 := by
    native_decide
  have hPostEquityGeInitialRaw :
      (Contracts.StorageWord.fromWord
          (s.storage
            (Contracts.structSlot2 3 (Contracts.StorageKey.toWord trader)
              (Contracts.StorageKey.toWord fundedAccountId) 1)) : Uint256) <=
        Verity.Core.Uint256.sub
          (Contracts.StorageWord.fromWord
            (s.storage
              (Contracts.structSlot2 3 (Contracts.StorageKey.toWord trader)
                (Contracts.StorageKey.toWord fundedAccountId) 3)))
          amount := by
    simpa [initialEquityAt, equityAt, HypernovaPayoutSystem.initialEquityOf,
      HypernovaPayoutSystem.equityOf, HypernovaPayoutSystem.structMember2,
      Contracts.structMember2At, Verity.bind, Bind.bind, Verity.pure,
      Pure.pure, Contract.run, ContractResult.fst, getStorage] using
      hPostEquityGeInitial
  simp [zeroAddress] at hPinnedVaultNonzero hConfiguredNonzero hTraderNonzero
  simp [fundedStatusAt, canWithdrawAt, equityAt, initialEquityAt,
    settledProfit, HypernovaPayoutSystem.fundedStatusOf,
    HypernovaPayoutSystem.canWithdrawOf, HypernovaPayoutSystem.equityOf,
    HypernovaPayoutSystem.initialEquityOf, HypernovaPayoutSystem.structMember2,
    HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
    HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
    Contracts.structMember2At, Verity.bind, Bind.bind, Verity.pure,
    Pure.pure, Contract.run, ContractResult.fst, getStorageAddr, getStorage,
    hVaultImmutable, hDomain, ACTIVE]
    at hStatusActive hStatusExists hCanWithdraw hEquity hAmountLeProfit
      hProfitSub hEquitySub
  simp [traderPayoutAmount, effectiveTraderSplit, BPS_DENOMINATOR]
    at hSplitAdd hSplitMul hTraderLeAmount hTraderAmountBalance hTraderAdd
      hVaultSub hProtocolSub
  simp [payoutRecoveredSigner, HypernovaPayoutSystem._recoverPayoutSigner,
    HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
    HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
    ContractResult.fst, getStorageAddr, getStorage,
    hVaultImmutable, hDomain] at hSigner
  unfold settledPayoutSafety
  constructor
  · unfold payoutResult
    simp [HypernovaPayoutSystem.requestPayout,
      HypernovaPayoutSystem._recoverPayoutSigner,
      HypernovaPayoutSystem._executePayout,
      HypernovaPayoutSystem.processPayout,
      HypernovaPayoutSystem.fundedStatusOf,
      HypernovaPayoutSystem.initialEquityOf,
      HypernovaPayoutSystem.equityOf,
      HypernovaPayoutSystem.canWithdrawOf,
      HypernovaPayoutSystem.structMember2,
      HypernovaPayoutSystem.setStructMember2,
      HypernovaPayoutSystem.vault,
      ACTIVE, BPS_DENOMINATOR,
      HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
      HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
      HypernovaPayoutSystem.userSuspended,
      HypernovaPayoutSystem.userExists,
      HypernovaPayoutSystem.userBonusBps,
      HypernovaPayoutSystem.nonces,
      HypernovaPayoutSystem.vaultPaused,
      HypernovaPayoutSystem.maxWithdrawalLimit,
      HypernovaPayoutSystem.profitSplit,
      HypernovaPayoutSystem.vaultUsdcBalance,
      HypernovaPayoutSystem.traderUsdcBalances,
      fundedStatusAt, initialEquityAt, equityAt, canWithdrawAt,
      effectiveTraderSplit, traderPayoutAmount, settledProfit,
      payoutRecoveredSigner, Contracts.structMember2At,
      Contracts.setStructMember2At,
      getMapping, setMapping, getStorage, getStorageAddr, setStorage,
      setStorageAddr, requireSomeUint, Verity.Stdlib.Math.requireSomeUint,
      HSub.hSub, blockTimestamp, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.fst,
      ContractResult.snd, ContractResult.isSuccess,
      hSuspended, hExists, hDeadline, hAmount, hConfiguredVault,
      hPinnedVaultNonzero, hConfiguredNonzero,
      hVaultImmutable, hVaultImmutableLiteral, hDomain, hDistinct,
      hStatusActive, hStatusExists,
      hActiveNonzeroLiteral, hCanWithdraw,
      hEquity, hAmountLeProfit, hSigner, hTotalBalance, hTraderNonzero,
      hAmountAllocated, hAmountAllocatedVal, hSplitAdd, hSplitMul,
      hTraderLeAmount,
      hTraderAmountBalance, hNonceAdd, hTraderAdd, hTransfer,
      hProfitSub, hEquitySub, hVaultSub, hProtocolSub]
  · simp [payoutResult,
      HypernovaPayoutSystem.requestPayout,
      HypernovaPayoutSystem._recoverPayoutSigner,
      HypernovaPayoutSystem._executePayout,
      HypernovaPayoutSystem.processPayout,
      HypernovaPayoutSystem.fundedStatusOf,
      HypernovaPayoutSystem.initialEquityOf,
      HypernovaPayoutSystem.equityOf,
      HypernovaPayoutSystem.canWithdrawOf,
      HypernovaPayoutSystem.structMember2,
      HypernovaPayoutSystem.setStructMember2,
      HypernovaPayoutSystem.vault,
      ACTIVE, BPS_DENOMINATOR,
      HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts,
      HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator,
      HypernovaPayoutSystem.userSuspended,
      HypernovaPayoutSystem.userExists,
      HypernovaPayoutSystem.userBonusBps,
      HypernovaPayoutSystem.nonces,
      HypernovaPayoutSystem.vaultPaused,
      HypernovaPayoutSystem.maxWithdrawalLimit,
      HypernovaPayoutSystem.profitSplit,
      HypernovaPayoutSystem.vaultUsdcBalance,
      HypernovaPayoutSystem.traderUsdcBalances,
      fundedStatusAt, initialEquityAt, equityAt, canWithdrawAt,
      effectiveTraderSplit, traderPayoutAmount, settledProfit,
      payoutRecoveredSigner, Contracts.structMember2At,
      Contracts.setStructMember2At,
      getMapping, setMapping, getStorage, getStorageAddr, setStorage,
      setStorageAddr, requireSomeUint, Verity.Stdlib.Math.requireSomeUint,
      HSub.hSub, blockTimestamp, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure, Contract.run, ContractResult.fst,
      ContractResult.snd, ContractResult.isSuccess,
      traderKey, accountKey,
      hSuspended, hExists, hDeadline, hAmount, hConfiguredVault,
      hPinnedVaultNonzero, hConfiguredNonzero,
      hVaultImmutable, hVaultImmutableLiteral, hDomain, hDistinct,
      hStatusActive, hStatusExists,
      hActiveNonzeroLiteral, hCanWithdraw,
      hEquity, hAmountLeProfit, hSigner, hTotalBalance, hTraderNonzero,
      hAmountAllocated, hAmountAllocatedVal, hSplitAdd, hSplitMul,
      hTraderLeAmount, hTraderAmountBalance, hNonceAdd, hTraderAdd,
      hTransfer, hProfitSub, hEquitySub, hVaultSub, hProtocolSub,
      hSlot0Ne3, hSlot0Ne4, hSlot1Ne3, hSlot1Ne4, hSlot3Ne4,
      hSlot4Ne3, hPostEquityGeInitial, hPostEquityGeInitialRaw, hOneSubOne]

/-- Every successful payout transfers no more than its authorized gross amount. -/
theorem successfulPayout_never_overpays
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool) :
    successfulPayoutNeverOverpays s trader fundedAccountId amount deadline v r signatureS
      transferSucceeds := by
  unfold successfulPayoutNeverOverpays
  intro _ _
  exact traderPayoutAmount_le_amount s trader amount

end Benchmark.Cases.Hypernova.SettledPayoutSafety
