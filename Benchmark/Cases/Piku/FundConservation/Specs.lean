import Verity.Specs.Common
import Benchmark.Cases.Piku.FundConservation.Contract

namespace Benchmark.Cases.Piku.FundConservation

open Verity
open Verity.EVM.Uint256

def initialBackingOf (s : ContractState) : Uint256 := s.storage 0
def distributedBackingOf (s : ContractState) : Uint256 := s.storage 1
def remainingBackingOf (s : ContractState) : Uint256 := s.storage 2
def protocolTreasuryFeesOf (s : ContractState) : Uint256 := s.storage 3
def projectTreasuryFeesOf (s : ContractState) : Uint256 := s.storage 4
def _openRedemptionAmountOf (s : ContractState) : Uint256 := s.storage 5
def _orderIdOf (s : ContractState) : Uint256 := s.storage 6
def sellFeeOf (s : ContractState) : Uint256 := s.storage 7

/--
Readable Piku fund-conservation accounting:
distributed backing + queued redemption backing + remaining backing +
protocol treasury fees + project treasury fees equals the initial backing
committed to this accounting pool.

`_openRedemptionAmount` is included as queued redemption backing because
Piku's Funding Manager creates manual queue payment orders before the
Payment Processor distributes collateral to users/protocol treasury.
-/
def fund_conservation_spec (s : ContractState) : Prop :=
  add
    (add (distributedBackingOf s) (_openRedemptionAmountOf s))
    (add (remainingBackingOf s)
      (add (protocolTreasuryFeesOf s) (projectTreasuryFeesOf s)))
    = initialBackingOf s

def sell_fee_split_spec
    (total protocolFeeBps projectFeeBps net protocol project : Uint256) : Prop :=
  protocol = protocolFeeAmount total protocolFeeBps ∧
  project = projectFeeAmount total projectFeeBps ∧
  net = netRedeemAmount total protocolFeeBps projectFeeBps ∧
  add (add net protocol) project = total

def sell_order_fund_conservation_arithmetic_spec
    (total protocolFeeBps : Uint256) (s : ContractState) : Prop :=
  let projectFeeBps := sellFeeOf s
  let protocol := protocolFeeAmount total protocolFeeBps
  let project := projectFeeAmount total projectFeeBps
  let net := netRedeemAmount total protocolFeeBps projectFeeBps
  fund_conservation_spec s →
  sell_fee_split_spec total protocolFeeBps projectFeeBps net protocol project →
  add
    (add (distributedBackingOf s)
      (add (_openRedemptionAmountOf s) (add net protocol)))
    (add (sub (remainingBackingOf s) total)
      (add (protocolTreasuryFeesOf s)
        (add (projectTreasuryFeesOf s) project)))
    = initialBackingOf s

def _sellOrder_preserves_fund_conservation_spec
    (total protocolFeeBps : Uint256) (s s' : ContractState) : Prop :=
  let projectFeeBps := sellFeeOf s
  let protocol := protocolFeeAmount total protocolFeeBps
  let project := projectFeeAmount total projectFeeBps
  let net := netRedeemAmount total protocolFeeBps projectFeeBps
  fund_conservation_spec s →
  sell_fee_split_spec total protocolFeeBps projectFeeBps net protocol project →
  sell_order_fund_conservation_arithmetic_spec total protocolFeeBps s →
  fund_conservation_spec s'

def _sellOrder_records_redemption_buckets_spec
    (total protocolFeeBps : Uint256) (s s' : ContractState) : Prop :=
  let projectFeeBps := sellFeeOf s
  let protocol := protocolFeeAmount total protocolFeeBps
  let project := projectFeeAmount total projectFeeBps
  let net := netRedeemAmount total protocolFeeBps projectFeeBps
  remainingBackingOf s' = sub (remainingBackingOf s) total ∧
  projectTreasuryFeesOf s' = add (projectTreasuryFeesOf s) project ∧
  _openRedemptionAmountOf s' =
    add (_openRedemptionAmountOf s) (add net protocol)

def amount_paid_fund_conservation_arithmetic_spec
    (amount protocolFeeAmount_ : Uint256) (s : ContractState) : Prop :=
  fund_conservation_spec s →
  add (sub amount protocolFeeAmount_) protocolFeeAmount_ = amount →
  add
    (add (add (distributedBackingOf s) (sub amount protocolFeeAmount_))
      (sub (_openRedemptionAmountOf s) amount))
    (add (remainingBackingOf s)
      (add (add (protocolTreasuryFeesOf s) protocolFeeAmount_)
        (projectTreasuryFeesOf s)))
    = initialBackingOf s

def amountPaid_preserves_fund_conservation_spec
    (amount protocolFeeAmount_ : Uint256) (s s' : ContractState) : Prop :=
  fund_conservation_spec s →
  add (sub amount protocolFeeAmount_) protocolFeeAmount_ = amount →
  amount_paid_fund_conservation_arithmetic_spec amount protocolFeeAmount_ s →
  fund_conservation_spec s'

def amountPaid_records_distribution_spec
    (amount protocolFeeAmount_ : Uint256) (s s' : ContractState) : Prop :=
  _openRedemptionAmountOf s' = sub (_openRedemptionAmountOf s) amount ∧
  distributedBackingOf s' =
    add (distributedBackingOf s) (sub amount protocolFeeAmount_) ∧
  protocolTreasuryFeesOf s' =
    add (protocolTreasuryFeesOf s) protocolFeeAmount_

end Benchmark.Cases.Piku.FundConservation
