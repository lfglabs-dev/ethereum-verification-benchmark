import Benchmark.Cases.Piku.FundConservation.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.Piku.FundConservation

open Verity
open Verity.EVM.Uint256

private theorem sell_fee_split_conserved
    (total protocol project : Uint256) :
    add (add (sub (sub total protocol) project) protocol) project = total := by
  change ((total - protocol - project) + protocol) + project = total
  rw [Verity.Core.Uint256.add_assoc]
  rw [Verity.Core.Uint256.add_comm protocol project]
  rw [← Verity.Core.Uint256.add_assoc]
  rw [Verity.Core.Uint256.sub_add_cancel_left]
  rw [Verity.Core.Uint256.sub_add_cancel_left]

private theorem pull_project_fee_into_sell_split
    (base queued remaining protocolFees projectFees project : Uint256) :
    (base + queued) + (remaining + (protocolFees + (projectFees + project))) =
    (base + (queued + project)) + (remaining + (protocolFees + projectFees)) := by
  calc
    (base + queued) + (remaining + (protocolFees + (projectFees + project)))
        = (base + queued) + (remaining + ((protocolFees + projectFees) + project)) := by
            rw [← Verity.Core.Uint256.add_assoc protocolFees projectFees project]
    _ = (base + queued) + ((remaining + (protocolFees + projectFees)) + project) := by
            rw [← Verity.Core.Uint256.add_assoc remaining (protocolFees + projectFees) project]
    _ = ((base + queued) + project) + (remaining + (protocolFees + projectFees)) := by
            rw [Verity.Core.Uint256.add_comm (remaining + (protocolFees + projectFees)) project]
            rw [← Verity.Core.Uint256.add_assoc]
    _ = (base + (queued + project)) + (remaining + (protocolFees + projectFees)) := by
            rw [Verity.Core.Uint256.add_assoc base queued project]

private theorem sell_total_move_conserved
    (base total remaining fees : Uint256) :
    (base + total) + ((remaining - total) + fees) = base + (remaining + fees) := by
  calc
    (base + total) + ((remaining - total) + fees)
        = base + (total + ((remaining - total) + fees)) := by
            rw [Verity.Core.Uint256.add_assoc]
    _ = base + (((remaining - total) + total) + fees) := by
            rw [← Verity.Core.Uint256.add_assoc total (remaining - total) fees]
            rw [Verity.Core.Uint256.add_comm total (remaining - total)]
    _ = base + (remaining + fees) := by
            rw [Verity.Core.Uint256.sub_add_cancel_left]

private theorem sell_transition_fund_conservation_arithmetic
    (distributed queued remaining protocolFees projectFees
      total protocol project : Uint256) :
    add
      (add distributed
        (add queued (add (sub (sub total protocol) project) protocol)))
      (add (sub remaining total)
        (add protocolFees (add projectFees project))) =
    add (add distributed queued)
      (add remaining (add protocolFees projectFees)) := by
  change
    (distributed + (queued + (((total - protocol) - project) + protocol))) +
      ((remaining - total) + (protocolFees + (projectFees + project))) =
    (distributed + queued) + (remaining + (protocolFees + projectFees))
  rw [show distributed + (queued + (((total - protocol) - project) + protocol)) =
      (distributed + queued) + (((total - protocol) - project) + protocol) by
        rw [← Verity.Core.Uint256.add_assoc]]
  rw [pull_project_fee_into_sell_split]
  rw [show total - protocol - project + protocol + project = total by
    exact sell_fee_split_conserved total protocol project]
  rw [sell_total_move_conserved]

private theorem pull_protocol_fee_into_payment_split
    (distributed userPaid queuedAfter remaining protocolFees projectFees protocolFee : Uint256) :
    ((distributed + userPaid) + queuedAfter) +
      (remaining + ((protocolFees + protocolFee) + projectFees)) =
    (distributed + (userPaid + protocolFee)) +
      (queuedAfter + (remaining + (protocolFees + projectFees))) := by
  calc
    ((distributed + userPaid) + queuedAfter) +
        (remaining + ((protocolFees + protocolFee) + projectFees))
        = (distributed + userPaid) +
            (queuedAfter + (remaining + ((protocolFees + protocolFee) + projectFees))) := by
              rw [Verity.Core.Uint256.add_assoc]
    _ = (distributed + userPaid) +
        (queuedAfter + (remaining + (protocolFee + (protocolFees + projectFees)))) := by
          rw [show (protocolFees + protocolFee) + projectFees =
              protocolFee + (protocolFees + projectFees) by
            rw [Verity.Core.Uint256.add_comm protocolFees protocolFee]
            rw [Verity.Core.Uint256.add_assoc protocolFee protocolFees projectFees]]
    _ = (distributed + userPaid) +
        (protocolFee + (queuedAfter + (remaining + (protocolFees + projectFees)))) := by
          rw [show queuedAfter + (remaining + (protocolFee + (protocolFees + projectFees))) =
              protocolFee + (queuedAfter + (remaining + (protocolFees + projectFees))) by
            rw [← Verity.Core.Uint256.add_assoc remaining protocolFee (protocolFees + projectFees)]
            rw [Verity.Core.Uint256.add_comm remaining protocolFee]
            rw [Verity.Core.Uint256.add_assoc protocolFee remaining (protocolFees + projectFees)]
            rw [← Verity.Core.Uint256.add_assoc queuedAfter protocolFee
              (remaining + (protocolFees + projectFees))]
            rw [Verity.Core.Uint256.add_comm queuedAfter protocolFee]
            rw [Verity.Core.Uint256.add_assoc protocolFee queuedAfter
              (remaining + (protocolFees + projectFees))]]
    _ = (distributed + (userPaid + protocolFee)) +
        (queuedAfter + (remaining + (protocolFees + projectFees))) := by
          rw [← Verity.Core.Uint256.add_assoc (distributed + userPaid) protocolFee
            (queuedAfter + (remaining + (protocolFees + projectFees)))]
          rw [show (distributed + userPaid) + protocolFee =
              distributed + (userPaid + protocolFee) by
            rw [Verity.Core.Uint256.add_assoc]]

private theorem amount_paid_transition_fund_conservation_arithmetic
    (distributed queued remaining protocolFees projectFees
      amount protocolFee : Uint256) :
    add (add (add distributed (sub amount protocolFee)) (sub queued amount))
      (add remaining (add (add protocolFees protocolFee) projectFees)) =
    add (add distributed queued)
      (add remaining (add protocolFees projectFees)) := by
  change
    ((distributed + (amount - protocolFee)) + (queued - amount)) +
      (remaining + ((protocolFees + protocolFee) + projectFees)) =
    (distributed + queued) + (remaining + (protocolFees + projectFees))
  rw [pull_protocol_fee_into_payment_split]
  rw [Verity.Core.Uint256.sub_add_cancel_left]
  calc
    (distributed + amount) +
        ((queued - amount) + (remaining + (protocolFees + projectFees)))
        = distributed +
            (amount + ((queued - amount) + (remaining + (protocolFees + projectFees)))) := by
              rw [Verity.Core.Uint256.add_assoc]
    _ = distributed + (((queued - amount) + amount) +
        (remaining + (protocolFees + projectFees))) := by
          rw [← Verity.Core.Uint256.add_assoc amount (queued - amount)
            (remaining + (protocolFees + projectFees))]
          rw [Verity.Core.Uint256.add_comm amount (queued - amount)]
    _ = distributed + (queued + (remaining + (protocolFees + projectFees))) := by
          rw [Verity.Core.Uint256.sub_add_cancel_left]
    _ = (distributed + queued) + (remaining + (protocolFees + projectFees)) := by
          rw [Verity.Core.Uint256.add_assoc]

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
  intro hConservation
  rcases _sellOrder_slot_write total protocolFeeBps s hAmount hFees hRemaining with
    ⟨hRemaining', hRest⟩
  rcases hRest with ⟨hProject', hRest⟩
  rcases hRest with ⟨hOpen', hRest⟩
  rcases hRest with ⟨hInitial', hRest⟩
  rcases hRest with ⟨hDistributed', hProtocol'⟩
  unfold fund_conservation_spec
  rw [hDistributed', hOpen', hRemaining', hProtocol', hProject', hInitial']
  unfold fund_conservation_spec at hConservation
  rw [← hConservation]
  simp [netRedeemAmount]
  exact sell_transition_fund_conservation_arithmetic
    (distributedBackingOf s) (_openRedemptionAmountOf s) (remainingBackingOf s)
    (protocolTreasuryFeesOf s) (projectTreasuryFeesOf s)
    total (protocolFeeAmount total protocolFeeBps)
    (projectFeeAmount total (sellFeeOf s))

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
  intro hConservation
  rcases amountPaid_slot_write amount protocolFeeAmount_ s hOpen hFee with
    ⟨hOpen', hRest⟩
  rcases hRest with ⟨hDistributed', hRest⟩
  rcases hRest with ⟨hProtocol', hRest⟩
  rcases hRest with ⟨hInitial', hRest⟩
  rcases hRest with ⟨hRemaining', hProject'⟩
  unfold fund_conservation_spec
  rw [hDistributed', hOpen', hRemaining', hProtocol', hProject', hInitial']
  unfold fund_conservation_spec at hConservation
  rw [← hConservation]
  exact amount_paid_transition_fund_conservation_arithmetic
    (distributedBackingOf s) (_openRedemptionAmountOf s) (remainingBackingOf s)
    (protocolTreasuryFeesOf s) (projectTreasuryFeesOf s)
    amount protocolFeeAmount_

end Benchmark.Cases.Piku.FundConservation
