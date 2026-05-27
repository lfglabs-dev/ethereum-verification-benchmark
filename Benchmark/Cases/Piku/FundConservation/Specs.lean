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

def _sellOrder_preserves_fund_conservation_spec
    (_total _protocolFeeBps : Uint256) (s s' : ContractState) : Prop :=
  fund_conservation_spec s →
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

def amountPaid_preserves_fund_conservation_spec
    (_amount _protocolFeeAmount_ : Uint256) (s s' : ContractState) : Prop :=
  fund_conservation_spec s →
  fund_conservation_spec s'

def amountPaid_records_distribution_spec
    (amount protocolFeeAmount_ : Uint256) (s s' : ContractState) : Prop :=
  _openRedemptionAmountOf s' = sub (_openRedemptionAmountOf s) amount ∧
  distributedBackingOf s' =
    add (distributedBackingOf s) (sub amount protocolFeeAmount_) ∧
  protocolTreasuryFeesOf s' =
    add (protocolTreasuryFeesOf s) protocolFeeAmount_

end Benchmark.Cases.Piku.FundConservation
