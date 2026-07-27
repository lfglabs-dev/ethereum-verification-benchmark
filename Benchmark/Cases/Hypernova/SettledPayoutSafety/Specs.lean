import Benchmark.Cases.Hypernova.SettledPayoutSafety.Contract

namespace Benchmark.Cases.Hypernova.SettledPayoutSafety

noncomputable section

open Verity hiding pure bind
open Verity.EVM.Uint256

/-- Read the modeled funded-account status from the composite state. -/
def fundedStatusAt (s : ContractState) (trader : Address) (fundedAccountId : Bytes32) : Uint256 :=
  ContractResult.fst (Contract.run (HypernovaPayoutSystem.fundedStatusOf trader fundedAccountId) s)

/-- Read the account's profit baseline. -/
def initialEquityAt (s : ContractState) (trader : Address) (fundedAccountId : Bytes32) : Uint256 :=
  ContractResult.fst (Contract.run (HypernovaPayoutSystem.initialEquityOf trader fundedAccountId) s)

/-- Read the account equity settled by the admin-fed accounting path. -/
def equityAt (s : ContractState) (trader : Address) (fundedAccountId : Bytes32) : Uint256 :=
  ContractResult.fst (Contract.run (HypernovaPayoutSystem.equityOf trader fundedAccountId) s)

/-- `1` means the settled account may currently request one payout. -/
def canWithdrawAt (s : ContractState) (trader : Address) (fundedAccountId : Bytes32) : Uint256 :=
  ContractResult.fst (Contract.run (HypernovaPayoutSystem.canWithdrawOf trader fundedAccountId) s)

/-- The gross amount earned above the account's initial-equity baseline. -/
def settledProfit (s : ContractState) (trader : Address) (fundedAccountId : Bytes32) : Uint256 :=
  sub (equityAt s trader fundedAccountId) (initialEquityAt s trader fundedAccountId)

/-- Basis points paid to the trader after the Vault's 100% clamp. -/
def effectiveTraderSplit (baseSplit bonusBps : Uint256) : Uint256 :=
  ite (add baseSplit bonusBps > BPS_DENOMINATOR)
    BPS_DENOMINATOR
    (add baseSplit bonusBps)

/-- Exact USDC transfer amount computed by `Vault.processPayout`. -/
def traderPayoutAmount
    (s : ContractState) (trader : Address) (grossAmount : Uint256) : Uint256 :=
  div
    (mul grossAmount
      (effectiveTraderSplit
        (s.storageMap 12 HypernovaPayoutSystem.pinnedVault)
        (s.storageMap 5 trader)))
    BPS_DENOMINATOR

/-- Execute the complete modeled payout path. -/
def payoutResult
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool) : ContractResult Unit :=
  Contract.run
    (HypernovaPayoutSystem.requestPayout trader fundedAccountId amount deadline
      v r signatureS transferSucceeds)
    s

/--
Signer recovered from the source payout tuple, consumed nonce, pinned EIP-712 domain,
and parsed signature words. On the proof side, body-less trusted uninterpreted
operations take every source input explicitly. Lean does not establish their Keccak,
EIP-712, ECDSA, injectivity, or semantic field-dependence properties. The compiler
model separately emits the source-shaped static-hash, digest, and recovery ECM chain.
-/
def payoutRecoveredSigner
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount nonce deadline v : Uint256) (r signatureS : Bytes32) : Address :=
  ContractResult.fst
    (Contract.run
      (HypernovaPayoutSystem._recoverPayoutSigner trader fundedAccountId amount nonce
        deadline v r signatureS)
      s)

/--
The composite internal `processPayout` represents the Vault's immutable
`onlyTradingAccounts` caller relation. This predicate pins both directions of the
verified deployment wiring, pins the payout domain separator, and excludes ERC-20
self-transfer aliasing between the trader and Vault.
-/
def pinnedDeploymentWiring (s : ContractState) (trader : Address) : Prop :=
  s.storageAddr 0 = HypernovaPayoutSystem.pinnedVault ∧
  s.storageAddr HypernovaPayoutSystem.__verity_immutable_slot_vaultTradingAccounts.slot =
    HypernovaPayoutSystem.pinnedTradingAccounts ∧
  s.storage HypernovaPayoutSystem.__verity_immutable_slot_payoutDomainSeparator.slot =
    HypernovaPayoutSystem.pinnedPayoutDomainSeparator ∧
  trader ≠ HypernovaPayoutSystem.pinnedVault

/--
The exact source guards and checked-arithmetic obligations for the modeled successful
path. The split-derived `traderAmount <= amount` bound is proved rather than assumed.
`payoutRecoveredSigner = trader` is the explicit proof-side cryptographic trust
boundary. Its body-less operations take the source tuple, consumed nonce, pinned
deployment domain, and parsed signature words as arguments; their cryptographic
semantics are not theorem conclusions.
`transferSucceeds = true` is the trusted native-USDC transfer boundary.
-/
def validSettledPayoutRequest
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool) : Prop :=
  let baseSplit := s.storageMap 12 HypernovaPayoutSystem.pinnedVault
  let bonusBps := s.storageMap 5 trader
  let totalSplit := effectiveTraderSplit baseSplit bonusBps
  let traderAmount := traderPayoutAmount s trader amount
  s.storageMap 2 trader = 1 ∧
  s.storageMap 4 trader = 0 ∧
  s.blockTimestamp <= deadline ∧
  amount ≠ 0 ∧
  pinnedDeploymentWiring s trader ∧
  fundedStatusAt s trader fundedAccountId = ACTIVE ∧
  canWithdrawAt s trader fundedAccountId = 1 ∧
  equityAt s trader fundedAccountId > initialEquityAt s trader fundedAccountId ∧
  amount <= settledProfit s trader fundedAccountId ∧
  payoutRecoveredSigner s trader fundedAccountId amount (s.storageMap 8 trader)
    deadline v r signatureS = trader ∧
  s.storageMap 10 HypernovaPayoutSystem.pinnedVault = 0 ∧
  trader ≠ zeroAddress ∧
  amount <= s.storageMap 11 HypernovaPayoutSystem.pinnedVault ∧
  safeAdd baseSplit bonusBps = some (add baseSplit bonusBps) ∧
  safeMul amount totalSplit = some (mul amount totalSplit) ∧
  traderAmount <= s.storageMap 13 HypernovaPayoutSystem.pinnedVault ∧
  safeAdd (s.storageMap 8 trader) 1 = some (add (s.storageMap 8 trader) 1) ∧
  safeAdd (s.storageMap 14 trader) traderAmount =
    some (add (s.storageMap 14 trader) traderAmount) ∧
  transferSucceeds = true

/--
English specification: after a valid settled payout, the requested gross amount is no
more than the settled profit; account equity decreases by that gross amount; the
one-shot withdrawal flag is closed; the signed nonce is consumed exactly once; and
the Vault debits exactly the same USDC amount that the trader receives, never more
than the gross request.
-/
def settledPayoutSafety
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool) : Prop :=
  let result := payoutResult s trader fundedAccountId amount deadline v r signatureS transferSucceeds
  let post := result.snd
  let traderAmount := traderPayoutAmount s trader amount
  result.isSuccess = true ∧
  traderAmount <= amount ∧
  amount <= settledProfit s trader fundedAccountId ∧
  equityAt post trader fundedAccountId = sub (equityAt s trader fundedAccountId) amount ∧
  initialEquityAt post trader fundedAccountId = initialEquityAt s trader fundedAccountId ∧
  equityAt post trader fundedAccountId >= initialEquityAt post trader fundedAccountId ∧
  fundedStatusAt post trader fundedAccountId = fundedStatusAt s trader fundedAccountId ∧
  canWithdrawAt post trader fundedAccountId = 0 ∧
  post.storageMap 8 trader = add (s.storageMap 8 trader) 1 ∧
  post.storageMap 13 HypernovaPayoutSystem.pinnedVault =
    sub (s.storageMap 13 HypernovaPayoutSystem.pinnedVault) traderAmount ∧
  post.storageMap 14 trader = add (s.storageMap 14 trader) traderAmount

/--
Independent success-path guard: no successful modeled call can transfer more to the
trader than the authorized gross request. The proof establishes the stronger arithmetic
fact directly from the split clamp, including modular `Uint256` multiplication.
-/
def successfulPayoutNeverOverpays
    (s : ContractState) (trader : Address) (fundedAccountId : Bytes32)
    (amount deadline v : Uint256) (r signatureS : Bytes32)
    (transferSucceeds : Bool) : Prop :=
  pinnedDeploymentWiring s trader →
  (payoutResult s trader fundedAccountId amount deadline v r signatureS transferSucceeds).isSuccess = true →
    traderPayoutAmount s trader amount <= amount

end


end Benchmark.Cases.Hypernova.SettledPayoutSafety
