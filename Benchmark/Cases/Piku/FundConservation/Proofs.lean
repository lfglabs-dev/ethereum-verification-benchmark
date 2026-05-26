import Benchmark.Cases.Piku.FundConservation.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Piku.FundConservation

open Verity
open Verity.EVM.Uint256

private theorem _sellOrder_slot_write
    (total protocolFeeBps : Uint256) (s : ContractState)
    (hAmount : total != 0)
    (hFees : add protocolFeeBps (s.storage 7) < 10000)
    (hRemaining : total.val <= (s.storage 2).val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1._sellOrder total protocolFeeBps).run s).snd
    remainingBackingOf s' = sub (remainingBackingOf s) total ∧
    projectTreasuryFeesOf s' =
      add (projectTreasuryFeesOf s) (projectFeeAmount total (sellFeeOf s)) ∧
    _openRedemptionAmountOf s' =
      add (_openRedemptionAmountOf s)
        (add (netRedeemAmount total protocolFeeBps (sellFeeOf s))
          (protocolFeeAmount total protocolFeeBps)) ∧
    initialBackingOf s' = initialBackingOf s ∧
    distributedBackingOf s' = distributedBackingOf s ∧
    protocolTreasuryFeesOf s' = protocolTreasuryFeesOf s := by
  repeat' constructor
  all_goals
    simp [FM_PC_Oracle_Redeeming_v1._sellOrder,
      FM_PC_Oracle_Redeeming_v1.remainingBacking,
      FM_PC_Oracle_Redeeming_v1.projectTreasuryFees,
      FM_PC_Oracle_Redeeming_v1._openRedemptionAmount,
      FM_PC_Oracle_Redeeming_v1._orderId,
      FM_PC_Oracle_Redeeming_v1.sellFee,
      initialBackingOf, distributedBackingOf, remainingBackingOf,
      protocolTreasuryFeesOf, projectTreasuryFeesOf,
      _openRedemptionAmountOf, sellFeeOf,
      netRedeemAmount, protocolFeeAmount, projectFeeAmount, BPS,
      hAmount, hFees, hRemaining,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      getStorage, setStorage]

theorem _sellOrder_records_redemption_buckets
    (total protocolFeeBps : Uint256) (s : ContractState)
    (hAmount : total != 0)
    (hFees : add protocolFeeBps (s.storage 7) < 10000)
    (hRemaining : total.val <= (s.storage 2).val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1._sellOrder total protocolFeeBps).run s).snd
    _sellOrder_records_redemption_buckets_spec total protocolFeeBps s s' := by
  rcases _sellOrder_slot_write total protocolFeeBps s hAmount hFees hRemaining with
    ⟨hRemaining', hRest⟩
  rcases hRest with ⟨hProject', hRest⟩
  rcases hRest with ⟨hOpen', _⟩
  simp [_sellOrder_records_redemption_buckets_spec, hRemaining', hProject', hOpen']

theorem _sellOrder_preserves_fund_conservation
    (total protocolFeeBps : Uint256) (s : ContractState)
    (hAmount : total != 0)
    (hFees : add protocolFeeBps (s.storage 7) < 10000)
    (hRemaining : total.val <= (s.storage 2).val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1._sellOrder total protocolFeeBps).run s).snd
    _sellOrder_preserves_fund_conservation_spec total protocolFeeBps s s' := by
  dsimp
  intro hConservation hSplit hArithmetic
  rcases _sellOrder_slot_write total protocolFeeBps s hAmount hFees hRemaining with
    ⟨hRemaining', hRest⟩
  rcases hRest with ⟨hProject', hRest⟩
  rcases hRest with ⟨hOpen', hRest⟩
  rcases hRest with ⟨hInitial', hRest⟩
  rcases hRest with ⟨hDistributed', hProtocol'⟩
  unfold fund_conservation_spec
  rw [hDistributed', hOpen', hRemaining', hProtocol', hProject', hInitial']
  exact hArithmetic hConservation hSplit

private theorem amountPaid_slot_write
    (amount protocolFeeAmount_ : Uint256) (s : ContractState)
    (hOpen : amount.val <= (s.storage 5).val)
    (hFee : protocolFeeAmount_.val <= amount.val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1.amountPaid amount protocolFeeAmount_).run s).snd
    _openRedemptionAmountOf s' = sub (_openRedemptionAmountOf s) amount ∧
    distributedBackingOf s' =
      add (distributedBackingOf s) (sub amount protocolFeeAmount_) ∧
    protocolTreasuryFeesOf s' =
      add (protocolTreasuryFeesOf s) protocolFeeAmount_ ∧
    initialBackingOf s' = initialBackingOf s ∧
    remainingBackingOf s' = remainingBackingOf s ∧
    projectTreasuryFeesOf s' = projectTreasuryFeesOf s := by
  repeat' constructor
  all_goals
    simp [FM_PC_Oracle_Redeeming_v1.amountPaid,
      FM_PC_Oracle_Redeeming_v1.distributedBacking,
      FM_PC_Oracle_Redeeming_v1.protocolTreasuryFees,
      FM_PC_Oracle_Redeeming_v1._openRedemptionAmount,
      initialBackingOf, distributedBackingOf, remainingBackingOf,
      protocolTreasuryFeesOf, projectTreasuryFeesOf,
      _openRedemptionAmountOf,
      hOpen, hFee,
      Verity.require, Verity.bind, Bind.bind, Contract.run, ContractResult.snd,
      getStorage, setStorage]

theorem amountPaid_records_distribution
    (amount protocolFeeAmount_ : Uint256) (s : ContractState)
    (hOpen : amount.val <= (s.storage 5).val)
    (hFee : protocolFeeAmount_.val <= amount.val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1.amountPaid amount protocolFeeAmount_).run s).snd
    amountPaid_records_distribution_spec amount protocolFeeAmount_ s s' := by
  rcases amountPaid_slot_write amount protocolFeeAmount_ s hOpen hFee with
    ⟨hOpen', hRest⟩
  rcases hRest with ⟨hDistributed', hRest⟩
  rcases hRest with ⟨hProtocol', _⟩
  simp [amountPaid_records_distribution_spec, hOpen', hDistributed', hProtocol']

theorem amountPaid_preserves_fund_conservation
    (amount protocolFeeAmount_ : Uint256) (s : ContractState)
    (hOpen : amount.val <= (s.storage 5).val)
    (hFee : protocolFeeAmount_.val <= amount.val) :
    let s' := ((FM_PC_Oracle_Redeeming_v1.amountPaid amount protocolFeeAmount_).run s).snd
    amountPaid_preserves_fund_conservation_spec amount protocolFeeAmount_ s s' := by
  dsimp
  intro hConservation hSplit hArithmetic
  rcases amountPaid_slot_write amount protocolFeeAmount_ s hOpen hFee with
    ⟨hOpen', hRest⟩
  rcases hRest with ⟨hDistributed', hRest⟩
  rcases hRest with ⟨hProtocol', hRest⟩
  rcases hRest with ⟨hInitial', hRest⟩
  rcases hRest with ⟨hRemaining', hProject'⟩
  unfold fund_conservation_spec
  rw [hDistributed', hOpen', hRemaining', hProtocol', hProject', hInitial']
  exact hArithmetic hConservation hSplit

end Benchmark.Cases.Piku.FundConservation
