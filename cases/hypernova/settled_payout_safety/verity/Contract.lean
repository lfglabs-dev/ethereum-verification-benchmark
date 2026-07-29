import Contracts.Common
import Compiler.Modules.Hashing
import Verity.Stdlib.Math

namespace Benchmark.Cases.Hypernova.SettledPayoutSafety

noncomputable section

open Verity hiding pure bind
open Verity.EVM.Uint256
open Compiler
open Contracts hiding ite blockTimestamp

abbrev requireSomeUint := Verity.Stdlib.Math.requireSomeUint
abbrev safeAdd := Verity.Stdlib.Math.safeAdd
abbrev safeSub := Verity.Stdlib.Math.safeSub
abbrev safeMul := Verity.Stdlib.Math.safeMul

/-!
Trusted proof-model shadows for the cryptographic ECMs used below. Verity's
compiler model carries the exact ABI, EIP-712, and precompile layouts, while the pinned
proof interpreter does not execute those ECMs. The axiomatic relations below therefore
make the exact source inputs visible in theorem hypotheses without reducing them to
Verity's additive default oracle or assigning fake executable bodies. Their intended
Keccak and ECDSA semantics remain an
explicit trust boundary.
-/

/-- Trusted relation for static ABI encoding followed by Keccak-256 on the exact words. -/
axiom payoutStaticHashOracleValue
    (typeHash traderWord fundedAccountId amount nonce deadline : Uint256) : Uint256

/-- Trusted relation for the EIP-712 domain-separated digest. -/
axiom payoutDigestOracleValue (domainSeparator structHash : Uint256) : Uint256

/-- Trusted relation for ECDSA recovery on the exact digest and `(v,r,s)`. -/
axiom payoutEcrecoverOracleValue
    (digest v r signatureS : Uint256) : Address

/-
These local rules replace only the proof-interpreter meaning of the exact call shapes.
The Verity translator still sees the raw calls and emits the package ECMs in
`_recoverPayoutSigner_modelBody`. The axioms have no executable bodies.
-/
local macro_rules
  | `(term| ecmCall
      (fun $_resultVar:ident => Compiler.Modules.Hashing.abiEncodeStaticWordsModule $_otherResultVar:ident 6)
      [$typeHash, $traderWord, $fundedAccountId, $amount, $nonce, $deadline]) =>
      `(term| Verity.pure (payoutStaticHashOracleValue
        $typeHash $traderWord $fundedAccountId $amount $nonce $deadline))
  | `(term| ecmCall Compiler.Modules.Hashing.eip712DigestModule [$domainSeparator, $structHash]) =>
      `(term| Verity.pure (payoutDigestOracleValue $domainSeparator $structHash))
  | `(term| ecrecover $digest $v $r $signatureS) =>
      `(term| Verity.pure (payoutEcrecoverOracleValue $digest $v $r $signatureS))

/-!
# Hypernova settled-payout system model

Source deployment on Arbitrum One:
- `TradingAccounts` proxy: `0x429d8f223acb622e5e748f6a7bdf1235b2334fcb`
- verified implementation: `0x8Ed9f54425c53ABE68AfE3fBD936e703C8775a5B`
- `Vault`: `0x920973eebffd3bf7da14dd9fb52bd3bea1664c67`
- native USDC: `0xaf88d065e77c8cC2239327C5EDb3A432268e5831`

The selected transition is
`TradingAccounts.requestPayout -> _executePayout -> Vault.processPayout -> USDC.safeTransfer`.

## Explicit simplifications and proof boundaries

1. The two deployed contracts and native USDC are represented by one composite
   `ContractState`. TradingAccounts keeps its source storage slots for modeled fields;
   Vault and token projections use disjoint model slots. This preserves the current
   verified cross-contract transition, including whole-transaction rollback, but does
   not claim safety after a proxy upgrade or owner-directed Vault rewiring. The spec
   pins both directions of the verified TradingAccounts/Vault wiring. The Vault's
   deployed `TRADING_ACCOUNTS` value is represented by a Verity immutable.
2. EIP-712 hashing follows the source payload exactly: payout type hash, trader,
   funded-account ID, amount, consumed nonce, and deadline are ABI-encoded as static
   words, then domain-separated with the pinned Arbitrum deployment separator before
   `ecrecover`. The compiler model uses Verity's hashing and precompile ECMs. The proof
   model uses narrow axiomatic relations with the same inputs and no executable bodies.
   Keccak correctness, ECDSA recovery, and Solady's 64/65-byte calldata parsing remain
   trusted boundaries;
   Solady does not impose a low-`s` check in this path.
3. Arbitrum native USDC `safeTransfer` is represented by `transferSucceeds` plus exact
   Vault and trader balance updates. Failure reverts the entire composite transaction.
   This model is not valid for fee-on-transfer or adversarial ERC-20 tokens. The spec
   excludes `trader == Vault`, where a real ERC-20 transfer would alias the two balances.
4. Events are omitted because the invariant concerns account state, nonce consumption,
   and token balance deltas. `protocolAmount = amount - traderAmount` is still evaluated
   with Solidity 0.8 checked subtraction after the modeled transfer, matching source
   order; `Contract.run` rolls all writes back if it fails.
5. The `FundedAccount` projection keeps the source `(address, bytes32)` nested key,
   exact word offsets, and packed status field. `canWithdraw` is the only source member
   in word 4 used or occupied by this layout, so the model stores its `0`/`1` value as
   the whole word rather than preserving unused upper padding bits. This is equivalent
   on canonical source-reachable states, where the cell begins at zero and source bool
   writes keep the upper padding zero. Arbitrary raw padding, assembly writes, and
   excluded upgrades are outside scope. Unread struct members are omitted and unclaimed.
6. Admin-fed settlement truth, off-chain P&L, flat-position detection, daily caps,
   reserve sufficiency beyond the transferred trader amount, and admin honesty are
   outside the theorem. `settled` means the pre-state storage flag `canWithdraw = true`.
-/

/-- Source enum value `FundedStatus.ACTIVE`. -/
def ACTIVE : Uint256 := 2

/-- Source basis-point denominator. -/
def BPS_DENOMINATOR : Uint256 := 10_000

verity_contract HypernovaPayoutSystem where
  storage
    vault : Address := slot 0
    userExists : Address → Uint256 := slot 2
    fundedAccounts : MappingStruct2(Address,Bytes32,[
      fundedStatus : Uint256 @word 0 packed(0,8),
      initialEquity : Uint256 @word 1,
      equity : Uint256 @word 3,
      canWithdraw : Uint256 @word 4
    ]) := slot 3
    userSuspended : Address → Uint256 := slot 4
    userBonusBps : Address → Uint256 := slot 5
    nonces : Address → Uint256 := slot 8

    -- Composite-model Vault and native-USDC projection. The pinned Vault address is
    -- a namespace key, so these separate deployed-contract fields cannot alias the
    -- TradingAccounts struct slots in the shared proof state.
    vaultPaused : Address → Uint256 := slot 10
    maxWithdrawalLimit : Address → Uint256 := slot 11
    profitSplit : Address → Uint256 := slot 12
    vaultUsdcBalance : Address → Uint256 := slot 13
    traderUsdcBalances : Address → Uint256 := slot 14

  constants
    pinnedVault : Address := 0x920973eebffd3bf7da14dd9fb52bd3bea1664c67
    pinnedTradingAccounts : Address := 0x429d8f223acb622e5e748f6a7bdf1235b2334fcb
    pinnedPayoutDomainSeparator : Bytes32 :=
      0x696cdb23dc932a7b83dc93dc2fc50f9efac628eb11e2a43c9d4b68c29e04fa02

  immutables
    vaultTradingAccounts : Address := pinnedTradingAccounts
    payoutDomainSeparator : Bytes32 := pinnedPayoutDomainSeparator

  function view fundedStatusOf
      (trader : Address, fundedAccountId : Bytes32) : Uint256 := do
    let value ← structMember2 "fundedAccounts" trader fundedAccountId "fundedStatus"
    return value

  function view initialEquityOf
      (trader : Address, fundedAccountId : Bytes32) : Uint256 := do
    let value ← structMember2 "fundedAccounts" trader fundedAccountId "initialEquity"
    return value

  function view equityOf
      (trader : Address, fundedAccountId : Bytes32) : Uint256 := do
    let value ← structMember2 "fundedAccounts" trader fundedAccountId "equity"
    return value

  function view canWithdrawOf
      (trader : Address, fundedAccountId : Bytes32) : Uint256 := do
    let value ← structMember2 "fundedAccounts" trader fundedAccountId "canWithdraw"
    return value

  /-
  Source-shaped EIP-712 payout recovery. The signature byte array is represented by
  its parsed `(v,r,s)` words; the exact source payload and pinned deployment domain
  remain part of the digest consumed by `ecrecover`.
  -/
  function internal _recoverPayoutSigner
      (trader : Address, fundedAccountId : Bytes32, amount : Uint256,
       nonce : Uint256, deadline : Uint256, v : Uint256,
       r : Bytes32, signatureS : Bytes32) : Address := do
    let structHash ← ecmCall
      (fun resultVar => Compiler.Modules.Hashing.abiEncodeStaticWordsModule resultVar 6)
      [keccakString
          "Payout(address trader,bytes32 fundedAccountId,uint256 amount,uint256 nonce,uint256 deadline)",
       addressToWord trader, fundedAccountId, amount, nonce, deadline]
    let digest ← ecmCall Compiler.Modules.Hashing.eip712DigestModule
      [payoutDomainSeparator, structHash]
    let signer ← ecrecover digest v r signatureS
    return signer

  /- Source-shaped `Vault.processPayout` for the verified wired Vault. -/
  function internal processPayout
      (trader : Address, amount : Uint256, bonusBps : Uint256,
       transferSucceeds : Bool) : Unit := do
    -- `Vault.onlyTradingAccounts`: this composite internal call represents the
    -- pinned TradingAccounts proxy as `msg.sender`.
    require (vaultTradingAccounts == pinnedTradingAccounts) "NotTradingAccounts"
    let paused ← getMapping vaultPaused pinnedVault
    require (paused == 0) "Paused"
    require (trader != Verity.zeroAddress) "ZeroAddress"
    let maxAmount ← getMapping maxWithdrawalLimit pinnedVault
    require (amount <= maxAmount) "ExceedsMaxWithdrawal"

    let baseSplit ← getMapping profitSplit pinnedVault
    let rawSplit ← requireSomeUint (safeAdd baseSplit bonusBps) "Panic(0x11)"
    let totalSplit := ite (rawSplit > 10_000) 10_000 rawSplit
    let splitProduct ← requireSomeUint (safeMul amount totalSplit) "Panic(0x11)"
    let traderAmount := div splitProduct 10_000

    let currentVaultBalance ← getMapping vaultUsdcBalance pinnedVault
    require (traderAmount <= currentVaultBalance) "InsufficientBalance"

    require transferSucceeds "USDCTransferFailed"

    let traderBalance ← getMapping traderUsdcBalances trader
    let newTraderBalance ← requireSomeUint (safeAdd traderBalance traderAmount) "Panic(0x11)"
    let newVaultBalance ← requireSomeUint (safeSub currentVaultBalance traderAmount) "Panic(0x11)"
    setMapping traderUsdcBalances trader newTraderBalance
    setMapping vaultUsdcBalance pinnedVault newVaultBalance

    -- Solidity computes this for `PayoutProcessed` after `safeTransfer`.
    -- `Contract.run` rolls the balance writes back if this checked subtraction fails.
    let _protocolAmount ← requireSomeUint (safeSub amount traderAmount) "Panic(0x11)"

  /- Source-shaped `TradingAccounts._executePayout`. -/
  function internal _executePayout
      (trader : Address, fundedAccountId : Bytes32, amount : Uint256,
       transferSucceeds : Bool) : Unit := do
    let canWithdraw ← canWithdrawOf trader fundedAccountId
    let fundedStatus ← fundedStatusOf trader fundedAccountId
    let equity ← equityOf trader fundedAccountId
    let initialEquity ← initialEquityOf trader fundedAccountId

    require (canWithdraw == 1) "CannotWithdraw"
    -- `verity_contract` bodies require the enum's source literal here.
    require (fundedStatus == 2) "FundedAccountNotActive"
    require (equity > initialEquity) "NoProfit"

    let profit ← requireSomeUint (safeSub equity initialEquity) "Panic(0x11)"
    require (amount <= profit) "ExceedsWithdrawableAmount"

    let newEquity ← requireSomeUint (safeSub equity amount) "Panic(0x11)"
    setStructMember2 "fundedAccounts" trader fundedAccountId "equity" newEquity
    let clearedFlag := sub canWithdraw canWithdraw
    setStructMember2 "fundedAccounts" trader fundedAccountId "canWithdraw" clearedFlag

    let bonusBps ← getMapping userBonusBps trader
    processPayout trader amount bonusBps transferSucceeds

  /-
  Source-shaped `TradingAccounts.requestPayout`.

  The EIP-712 digest and signer recovery are computed from the exact signed fields and
  the consumed nonce. The source signature byte array is represented by `(v,r,s)`.
  -/
  function requestPayout
      (trader : Address, fundedAccountId : Bytes32, amount : Uint256, deadline : Uint256,
       v : Uint256, r : Bytes32, signatureS : Bytes32,
       transferSucceeds : Bool) : Unit := do
    let suspended ← getMapping userSuspended trader
    require (suspended == 0) "UserIsSuspended"
    let userExistsFlag ← getMapping userExists trader
    require (userExistsFlag == 1) "UserAccountDoesNotExist"

    let currentTimestamp ← blockTimestamp
    require (currentTimestamp <= deadline) "SignatureExpired"
    require (amount != 0) "ZeroAmount"
    let configuredVault ← getStorageAddr vault
    require (configuredVault != Verity.zeroAddress) "VaultNotSet"

    let fundedStatus ← fundedStatusOf trader fundedAccountId
    require (fundedStatus != 0) "FundedAccountIdDoesNotExist"

    -- Solidity evaluates `nonces[trader]++` while building the signed payload.
    let nonce ← getMapping nonces trader
    let nextNonce ← requireSomeUint (safeAdd nonce 1) "Panic(0x11)"
    setMapping nonces trader nextNonce

    let recoveredSigner ←
      _recoverPayoutSigner trader fundedAccountId amount nonce deadline v r signatureS
    require (recoveredSigner == trader) "InvalidSignature"
    _executePayout trader fundedAccountId amount transferSucceeds

end

end Benchmark.Cases.Hypernova.SettledPayoutSafety
