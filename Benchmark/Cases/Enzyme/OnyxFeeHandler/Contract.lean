import Contracts.Common

namespace Benchmark.Cases.Enzyme.OnyxFeeHandler

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

set_option linter.unusedVariables false

/-!
# Enzyme Onyx FeeHandler dynamic-fee settlement

Source of truth:
- repository: https://github.com/enzymefinance/protocol-onyx
- commit: 8ae6f589b13a19d8390eb0956836c6a9f48fadab
- source: src/components/fees/FeeHandler.sol
- selected functions: `settleDynamicFeesGivenPositionsValue`,
  `__increaseValueOwed`, and `__updateValueOwed`

Simplifications and their justification:

1. The ERC-7201 `FeeHandlerStorage` struct is flattened to logical storage
   slots. Field identity, address-keyed fee liabilities, helper boundaries, and
   sequential writes are preserved. Slot-hash collision freedom is outside
   this accounting theorem.
2. The inherited `__getShares()` result is an explicit `shares` semantic-model
   parameter. The nested `Shares.getValuationHandler()` read and both tracker
   calls query arbitrary responses from `Verity.Env.callOracle`. Every query
   includes the dynamic target, exact ABI selector, and exact argument words.
   Pinned Verity does support ABI-faithful runtime-target static-word calls.
   This model deliberately uses the oracle path because the executable helper
   semantics do not provide arbitrary environmental returndata for this theorem.
   A successful oracle branch supplies one full return word; short or malformed
   returndata and ABI-decode failures are folded into the call-failure outcome.
   `wordToAddress` projects the low 160 bits of valuation-handler returndata,
   so the semantic model also admits non-canonical ABI address words that
   Solidity would reject. This is a conservative over-approximation of
   successful source executions.
3. The valuation-handler lookup is modeled as a state-preserving static call,
   matching Solidity's `STATICCALL`. Successful tracker calls apply
   `Env.reenter` to FeeHandler state. Exact accounting does not assume that hook
   is `id`; instead it uses the projection-level rely condition in `Specs.lean`,
   which permits arbitrary changes outside the six dynamic-fee storage
   projections needed by the theorem. Callee storage, timestamps, rates, and
   high-water marks remain outside this single-contract model.
4. `ManagementFeeSettled`, `PerformanceFeeSettled`,
   `UserValueOwedUpdated`, and `TotalValueOwedUpdated` are omitted because they
   do not affect the liability state proved here.
5. Entrance, exit, and claim paths are omitted. The case targets only dynamic
   management/performance settlement.

All fee arithmetic uses full-width `Uint256`, matching the source. Explicit
subtraction guards and `safeAdd` model Solidity 0.8.28 checked arithmetic on
successful execution.
-/

/-- `Shares.getValuationHandler()` ABI selector. -/
def getValuationHandlerSelector : Uint256 := 0xc2e92265

/-- `IManagementFeeTracker.settleManagementFee(uint256)` ABI selector. -/
def settleManagementFeeSelector : Uint256 := 0xf7ebf0cf

/-- `IPerformanceFeeTracker.settlePerformanceFee(uint256)` ABI selector. -/
def settlePerformanceFeeSelector : Uint256 := 0x6655aa9a

/-- The semantic key of one external word-returning call. -/
def externalCallKeyWords
    (target : Address) (selector : Uint256) (arguments : List Uint256) : List Uint256 :=
  addressToWord target :: selector :: arguments

/-- Arbitrary environment-controlled success for an exact call identity. -/
def externalCallSucceeded
    (env : Verity.Env)
    (target : Address) (selector : Uint256) (arguments : List Uint256) : Bool :=
  env.callOracle "externalCallSucceeded" (externalCallKeyWords target selector arguments) != 0

/-- Arbitrary environment-controlled returndata for an exact call identity. -/
def externalCallReturndata
    (env : Verity.Env)
    (target : Address) (selector : Uint256) (arguments : List Uint256) : Uint256 :=
  env.callOracle "externalCallReturndata" (externalCallKeyWords target selector arguments)

/-- Execute a state-changing environment call and apply its possible reentry hook. -/
def runExternalWordCall
    (env : Verity.Env)
    (target : Address)
    (selector : Uint256)
    (arguments : List Uint256) : Contract Uint256 := fun s =>
  if externalCallSucceeded env target selector arguments then
    ContractResult.success
      (externalCallReturndata env target selector arguments)
      (env.reenter s)
  else
    ContractResult.revert "external-call-reverted" s

/-- Execute a `STATICCALL`-like environment read. Successful static calls cannot
    mutate any contract state, including through a nested callback. -/
def runStaticWordCall
    (env : Verity.Env)
    (target : Address)
    (selector : Uint256)
    (arguments : List Uint256) : Contract Uint256 := fun s =>
  if externalCallSucceeded env target selector arguments then
    ContractResult.success
      (externalCallReturndata env target selector arguments)
      s
  else
    ContractResult.revert "external-staticcall-reverted" s

verity_contract FeeHandler where
  storage
    managementFeeTracker : Address := slot 0
    performanceFeeTracker : Address := slot 1
    managementFeeRecipient : Address := slot 2
    performanceFeeRecipient : Address := slot 3
    totalFeesOwed : Uint256 := slot 4
    userFeesOwed : Address → Uint256 := slot 5

  /- Preserves Solidity `__updateValueOwed` as its own helper boundary. -/
  function internal __updateValueOwed
      (user : Address, userValueOwed : Uint256, totalValueOwed : Uint256) : Unit := do
    setMapping userFeesOwed user userValueOwed
    setStorage totalFeesOwed totalValueOwed

  /- Preserves Solidity `__increaseValueOwed`, including checked additions. -/
  function internal __increaseValueOwed (user : Address, delta : Uint256) : Unit := do
    let userValueOwed ← getMapping userFeesOwed user
    let updatedUserValueOwed ←
      requireSomeUint (safeAdd userValueOwed delta) "user-fees-overflow"

    let totalValueOwed ← getStorage totalFeesOwed
    let updatedTotalValueOwed ←
      requireSomeUint (safeAdd totalValueOwed delta) "total-fees-overflow"

    __updateValueOwed user updatedUserValueOwed updatedTotalValueOwed

namespace FeeHandler

/--
Semantic model of Solidity `settleDynamicFeesGivenPositionsValue` lines
217-248. `shares` models the inherited immutable Shares address; `env` supplies
the nested authorization and optional tracker responses. Both optional branches,
post-call recipient reads, and management-before-performance ordering match the
source.
-/
def settleDynamicFeesGivenPositionsValue
    (env : Verity.Env)
    (totalPositionsValue : Uint256)
    (shares : Address)
    : Contract Unit := do
  let sender ← msgSender
  let valuationHandlerWord ←
    runStaticWordCall env shares getValuationHandlerSelector []
  require (sender == wordToAddress valuationHandlerWord) "unauthorized"

  let preTotalFeesOwed ← getStorage totalFeesOwed
  require (preTotalFeesOwed <= totalPositionsValue) "positions-value-underflow"
  let netValue := sub totalPositionsValue preTotalFeesOwed

  let managementTrackerForBranch ← getStorageAddr managementFeeTracker
  let mut managementFeeAmount : Uint256 := 0
  if managementTrackerForBranch != zeroAddress then
    let managementTrackerForCall ← getStorageAddr managementFeeTracker
    managementFeeAmount ← runExternalWordCall
      env managementTrackerForCall settleManagementFeeSelector [netValue]
    let managementRecipient ← getStorageAddr managementFeeRecipient
    __increaseValueOwed managementRecipient managementFeeAmount

  let performanceTrackerForBranch ← getStorageAddr performanceFeeTracker
  if performanceTrackerForBranch != zeroAddress then
    require (managementFeeAmount <= netValue) "performance-net-value-underflow"
    let performanceNetValue := sub netValue managementFeeAmount
    let performanceTrackerForCall ← getStorageAddr performanceFeeTracker
    let performanceFeeAmount ← runExternalWordCall
      env performanceTrackerForCall settlePerformanceFeeSelector [performanceNetValue]
    let performanceRecipient ← getStorageAddr performanceFeeRecipient
    __increaseValueOwed performanceRecipient performanceFeeAmount
  else
    return ()

end FeeHandler

end Benchmark.Cases.Enzyme.OnyxFeeHandler