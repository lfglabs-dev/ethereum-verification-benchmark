import Contracts.Common

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity hiding pure bind
open Verity.EVM.Uint256

def UINT32_MAX_WORD : Uint256 := 4294967295
def INT96_MAX_WORD : Uint256 := 39614081257132168796771975167
def NEG_INT96_MIN_WORD : Uint256 :=
  115792089237316195423570985008687907853269984665600949958200451839116357664768
def INT256_SIGN_BIT_WORD : Uint256 :=
  57896044618658097711785492504343953926634992332820282019728792003956564819968
def DEPOSIT_LOW_MASK : Uint256 := 4294967295
def PACKED_DEPOSIT_MAX : Uint256 := 79228162514264337589248983040

/-- A positive source `int96`, represented as an EVM word. -/
def isPositiveInt96Word (value : Uint256) : Bool :=
  value != 0 && value <= INT96_MAX_WORD

/-- A sign-extended source `int96`, represented as an EVM word. -/
def isCanonicalInt96Word (value : Uint256) : Bool :=
  value <= INT96_MAX_WORD || value >= NEG_INT96_MIN_WORD

/-- The sign bit is clear, so the EVM word denotes a nonnegative `int256`. -/
def isNonnegativeInt256Word (value : Uint256) : Bool :=
  value < INT256_SIGN_BIT_WORD

/-- Signed addition cannot overflow when equal-sign operands retain that sign. -/
def signedAddNoOverflow (left right : Uint256) : Bool :=
  let leftNonnegative := isNonnegativeInt256Word left
  let rightNonnegative := isNonnegativeInt256Word right
  let resultNonnegative := isNonnegativeInt256Word (add left right)
  if leftNonnegative == rightNonnegative then
    resultNonnegative == leftNonnegative
  else
    true

/-- Signed subtraction cannot overflow when opposite-sign operands retain the left sign. -/
def signedSubNoOverflow (left right : Uint256) : Bool :=
  let leftNonnegative := isNonnegativeInt256Word left
  let rightNonnegative := isNonnegativeInt256Word right
  let resultNonnegative := isNonnegativeInt256Word (sub left right)
  if leftNonnegative != rightNonnegative then
    resultNonnegative == leftNonnegative
  else
    true

/-- Canonical decoded CFA deposit/owed-deposit: 64 stored bits followed by 32 zero bits. -/
def isPackedDepositWord (value : Uint256) : Bool :=
  mod value 4294967296 == 0 && value <= PACKED_DEPOSIT_MAX

/-- Solidity `_clipDepositNumberRoundingUp`. -/
def clipDepositRoundingUp (deposit : Uint256) : Uint256 :=
  let rounding : Uint256 :=
    if mod deposit 4294967296 > 0 then 1 else 0
  mul (add (div deposit 4294967296) rounding) 4294967296

/-- Solidity `_calculateDeposit` plus the minimum-deposit branch in `_changeFlow`.
The executable wrappers separately require the positive `int96` product to fit. -/
def sourceDeposit
    (flowRate liquidationPeriod minimumDeposit : Uint256) : Uint256 :=
  if flowRate == 0 then 0 else
    let calculated := clipDepositRoundingUp (mul flowRate liquidationPeriod)
    if calculated < minimumDeposit then minimumDeposit else calculated

/-- Deposit value observed after Solidity `_encodeFlowData` followed by decode. -/
def sourceStoredDeposit (deposit : Uint256) : Uint256 :=
  mul (mod (div deposit 4294967296) 18446744073709551616) 4294967296

/-- Regression witness for the callback-credit path: when the minimum binds, Solidity
grants the clipped pre-minimum `appCreditBase`, not the larger stored deposit. -/
theorem appCreditBase_differs_when_minimumBinds :
    clipDepositRoundingUp (mul 1 1) = 4294967296 ∧
    sourceDeposit 1 1 8589934592 = 8589934592 ∧
    clipDepositRoundingUp (mul 1 1) ≠ sourceDeposit 1 1 8589934592 := by
  decide

/-- Regression witness that an arbitrary unaligned governance minimum is selected
before the source's low-64-bit deposit storage encoding. -/
theorem unalignedMinimum_is_encoded_on_storageWrite :
    sourceDeposit 1 1 8589934593 = 8589934593 ∧
    sourceStoredDeposit (sourceDeposit 1 1 8589934593) = 8589934592 := by
  decide

/-- Boundary witness for the benchmark's no-field-overlap scope. At `2^96`, the
source deposit field wraps and its unmasked high bit would overlap the flow-rate field. -/
theorem depositFieldBoundary_wrapsAtTwoPow96 :
    sourceStoredDeposit 79228162514264337593543950335 = PACKED_DEPOSIT_MAX ∧
    sourceStoredDeposit 79228162514264337593543950336 = 0 := by
  decide

/-!
Source-faithful decoded CFA slice pinned to Superfluid protocol-monorepo
`414109689d9041a8b6900b67b947f3f203c1da5d`:

* `SuperfluidToken.sol:73-105,315-324` for native realtime-balance aggregation and
  shared settled balances.
* `ConstantFlowAgreementV1.sol:411-570,980-1040,1060-1176,1210-1341,1343-1357,
  1445-1467,1481-1523` for create/update/delete guards, CFA settlement, deposit
  calculation, app callbacks, availability checks, and packed flow data.
* `contracts/mocks/CFAAppMocks.t.sol:190-243` for the concrete create-only
  `SelfDeletingFlowTestApp` callback schedule.

Storage slots 0-9 are decoded SuperToken/CFA fields. Slots 10-31 are an explicit
source-environment relation to Host app registry/config/context facts; they are not
claimed to be CFA storage.

Deliberate simplifications and scope:

1. The theorem projection is `sharedSettled + CFA dynamic balance`, not the native
   `SuperfluidToken.realtimeBalanceOf` available-balance return. Availability guards
   are modeled under an explicit CFA-only/no-other-agreement assumption, with zero
   account owed deposit.
2. Pair/account fields are decoded from source packed words into mappings. The case
   restricts the Host timestamp to the canonical uint32 chain-time range, while the
   source itself accepts uint256 and packs the low 32 bits. Every executable entrypoint
   enforces canonical int96 rates, clipped decoded deposit words, existence,
   zero-address, and checked signed-word conditions needed by the represented path.
3. Governance inputs `liquidationPeriod` and `minimumDeposit` remain explicit, but
   the model computes `_calculateDeposit`, clipping, and the minimum rule itself. The
   benchmark restricts raw flow/account deposit writes below `2^96`; larger governance
   values are source-accepted but their unmasked packed bits overlap adjacent fields.
4. Host dispatch is represented by decoded `isApp`, `isJailed`, outer direct-call
   context, callback-config, and callback-credit facts. The callback is the exact
   create-only SelfDeleting app:
   before-created is NOOP, after-created deletes the same flow through Host context,
   recursive callback is suppressed, outer code reloads the final zero flow, and
   app-credit used is zero.
5. Update callbacks, arbitrary external callback code, IDA/GDA and pools, critical
   delete/liquidation, mint/burn, wrapping, and multi-agreement max aggregation are
   outside this case. Third-account frame specs cover account projection fields, not
   unrelated pair-flow mappings.
-/
verity_contract SuperfluidCFA where
  storage
    -- Decoded SuperToken/CFA state.
    sharedSettledBalances : Address → Uint256 := slot 0
    accountNetFlowRates : Address → Uint256 := slot 1
    accountTimestamps : Address → Uint256 := slot 2
    accountDeposits : Address → Uint256 := slot 3
    accountOwedDeposits : Address → Uint256 := slot 4
    flowTimestamps : Address → Address → Uint256 := slot 5
    flowRates : Address → Address → Uint256 := slot 6
    flowDeposits : Address → Address → Uint256 := slot 7
    flowOwedDeposits : Address → Address → Uint256 := slot 8
    flowExists : Address → Address → Uint256 := slot 9

    -- Decoded Host/environment relation for the pinned callback schedule.
    hostIsApp : Address → Uint256 := slot 10
    hostIsJailed : Address → Uint256 := slot 11
    hostBeforeCreatedNoop : Address → Uint256 := slot 12
    hostAfterCreatedEnabled : Address → Uint256 := slot 13
    hostCallbackCreditUsed : Address → Uint256 := slot 14
    hostCallbackLevel : Address → Uint256 := slot 15
    hostCallbackActor : Address → Uint256 := slot 16
    hostCallbackAppAddress : Address → Uint256 := slot 17
    hostIsAppCallbackContext : Address → Uint256 := slot 18
    hostContextualDeleteEnabled : Address → Uint256 := slot 19
    hostNestedCallbackSuppressed : Address → Uint256 := slot 20
    hostAppCreditTokenMatches : Address → Uint256 := slot 21
    hostAppCreditGranted : Address → Uint256 := slot 22
    hostAdditionalAppCredit : Address → Uint256 := slot 23
    governanceLiquidationPeriod : Uint256 := slot 24
    governanceMinimumDeposit : Uint256 := slot 25
    sourceCfaOnlyActiveAgreement : Uint256 := slot 26
    sourceFlowKeyMatches : Address → Address → Uint256 := slot 27
    hostIsSelfDeletingFlowApp : Address → Uint256 := slot 28
    hostOuterIsDirectCallContext : Uint256 := slot 29
    hostOuterAppCreditToken : Uint256 := slot 30
    hostOuterActor : Uint256 := slot 31

  function internal _requireSourceEnvironment
      (sender : Address, receiver : Address, liquidationPeriod : Uint256,
       minimumDeposit : Uint256) : Unit := do
    let cfaOnly ← getStorage sourceCfaOnlyActiveAgreement
    let flowKeyMatches ← getMapping2 sourceFlowKeyMatches sender receiver
    let configuredLiquidationPeriod ← getStorage governanceLiquidationPeriod
    let configuredMinimumDeposit ← getStorage governanceMinimumDeposit
    require (cfaOnly == 1) "SOURCE_CFA_ONLY_ACTIVE"
    require (flowKeyMatches == 1) "SOURCE_FLOW_KEY_MISMATCH"
    require (configuredLiquidationPeriod == liquidationPeriod) "SOURCE_LIQUIDATION_PERIOD"
    require (configuredMinimumDeposit == minimumDeposit) "SOURCE_MINIMUM_DEPOSIT"
    require (minimumDeposit < 79228162514264337593543950336)
      "BENCHMARK_MINIMUM_DEPOSIT_NO_FIELD_OVERLAP_SCOPE"

  function internal _requireDirectOuterHostContext (sender : Address) : Unit := do
    let isDirectCallContext ← getStorage hostOuterIsDirectCallContext
    let appCreditToken ← getStorage hostOuterAppCreditToken
    let actor ← getStorage hostOuterActor
    require (isDirectCallContext == 1) "HOST_OUTER_CONTEXT_NOT_DIRECT"
    require (appCreditToken == 0) "HOST_OUTER_APP_CREDIT_TOKEN"
    require (actor == sender) "HOST_OUTER_ACTOR"

  function internal _requireCanonicalAccount (account : Address) : Unit := do
    let timestamp ← getMapping accountTimestamps account
    let netFlowRate ← getMapping accountNetFlowRates account
    let deposit ← getMapping accountDeposits account
    let owedDeposit ← getMapping accountOwedDeposits account
    require (timestamp <= 4294967295) "CFA_TIMESTAMP_PACKING"
    require (netFlowRate <= 39614081257132168796771975167 ||
      netFlowRate >= 115792089237316195423570985008687907853269984665600949958200451839116357664768)
      "CFA_NET_FLOW_RATE_PACKING"
    require (mod deposit 4294967296 == 0 &&
      deposit <= 79228162514264337589248983040) "CFA_DEPOSIT_PACKING"
    require (mod owedDeposit 4294967296 == 0 &&
      owedDeposit <= 79228162514264337589248983040) "CFA_OWED_DEPOSIT_PACKING"

  function internal _requireEmptyFlow (sender : Address, receiver : Address) : Unit := do
    let existsWord ← getMapping2 flowExists sender receiver
    let timestamp ← getMapping2 flowTimestamps sender receiver
    let rate ← getMapping2 flowRates sender receiver
    let deposit ← getMapping2 flowDeposits sender receiver
    let owedDeposit ← getMapping2 flowOwedDeposits sender receiver
    require (existsWord == 0) "CFA_FLOW_ALREADY_EXISTS"
    require (timestamp == 0) "CFA_EMPTY_FLOW_TIMESTAMP"
    require (rate == 0) "CFA_EMPTY_FLOW_RATE"
    require (deposit == 0) "CFA_EMPTY_FLOW_DEPOSIT"
    require (owedDeposit == 0) "CFA_EMPTY_FLOW_OWED"

  function internal _requireExistingZeroOwedFlow (sender : Address, receiver : Address) : Unit := do
    let existsWord ← getMapping2 flowExists sender receiver
    let timestamp ← getMapping2 flowTimestamps sender receiver
    let rate ← getMapping2 flowRates sender receiver
    let deposit ← getMapping2 flowDeposits sender receiver
    let owedDeposit ← getMapping2 flowOwedDeposits sender receiver
    require (existsWord == 1) "CFA_FLOW_DOES_NOT_EXIST"
    require (timestamp <= 4294967295) "CFA_FLOW_TIMESTAMP_PACKING"
    require (rate != 0 && rate <= 39614081257132168796771975167) "CFA_FLOW_RATE_PACKING"
    require (mod deposit 4294967296 == 0 &&
      deposit <= 79228162514264337589248983040) "CFA_FLOW_DEPOSIT_PACKING"
    require (owedDeposit == 0) "CFA_NON_APP_OWED_DEPOSIT"

  function internal _calculateSourceAppCreditBase
      (flowRate : Uint256, liquidationPeriod : Uint256) : Uint256 := do
    require (liquidationPeriod <= 39614081257132168796771975167) "CFA_LIQUIDATION_PERIOD_INT96"
    require (mul flowRate liquidationPeriod <= 39614081257132168796771975167)
      "CFA_DEPOSIT_INT96_OVERFLOW"
    if flowRate == 0 then
      return 0
    else
      let rawDeposit := mul flowRate liquidationPeriod
      let lowBits := mod rawDeposit 4294967296
      if lowBits > 0 then
        let calculated := mul (add (div rawDeposit 4294967296) 1) 4294967296
        return calculated
      else
        let calculated := mul (div rawDeposit 4294967296) 4294967296
        return calculated

  function internal _calculateSourceDeposit
      (flowRate : Uint256, liquidationPeriod : Uint256, minimumDeposit : Uint256) : Uint256 := do
    let appCreditBase ← _calculateSourceAppCreditBase flowRate liquidationPeriod
    if appCreditBase < minimumDeposit && flowRate > 0 then
      return minimumDeposit
    else
      return appCreditBase

  function internal _settleBalance (account : Address, deltaWord : Uint256) : Unit := do
    let oldSettledWord ← getMapping sharedSettledBalances account
    let newSettledWord := add oldSettledWord deltaWord
    let oldNonnegative := oldSettledWord <
      57896044618658097711785492504343953926634992332820282019728792003956564819968
    let deltaNonnegative := deltaWord <
      57896044618658097711785492504343953926634992332820282019728792003956564819968
    let newNonnegative := newSettledWord <
      57896044618658097711785492504343953926634992332820282019728792003956564819968
    if oldNonnegative == deltaNonnegative then
      require (newNonnegative == oldNonnegative) "CFA_SETTLED_BALANCE_OVERFLOW"
    else
      pure ()
    setMapping sharedSettledBalances account newSettledWord

  function internal _updateAccountFlowState
      (account : Address, flowRateDelta : Uint256, depositDelta : Uint256,
       owedDepositDelta : Uint256, currentTimestamp : Uint256) : Unit := do
    _requireCanonicalAccount account
    let oldTimestamp ← getMapping accountTimestamps account
    let oldNetFlowRateWord ← getMapping accountNetFlowRates account
    require (currentTimestamp <= 4294967295) "BENCHMARK_CANONICAL_TIMESTAMP_SCOPE"
    require (currentTimestamp >= oldTimestamp) "CFA_TIMESTAMP_UNDERFLOW"
    let elapsed := sub currentTimestamp oldTimestamp
    let dynamicBalanceWord := mul elapsed oldNetFlowRateWord
    if dynamicBalanceWord != 0 then
      _settleBalance account dynamicBalanceWord
    else
      pure ()
    let newNetFlowRateWord := add oldNetFlowRateWord flowRateDelta
    require (newNetFlowRateWord <= 39614081257132168796771975167 ||
      newNetFlowRateWord >= 115792089237316195423570985008687907853269984665600949958200451839116357664768)
      "CFA_NET_FLOW_RATE_OVERFLOW"
    setMapping accountNetFlowRates account newNetFlowRateWord
    setMapping accountTimestamps account currentTimestamp
    let oldDepositWord ← getMapping accountDeposits account
    let newDepositWord := add oldDepositWord depositDelta
    require (newDepositWord < 79228162514264337593543950336)
      "BENCHMARK_ACCOUNT_DEPOSIT_NO_FIELD_OVERLAP_SCOPE"
    let storedDepositWord := mul
      (mod (div newDepositWord 4294967296) 18446744073709551616) 4294967296
    setMapping accountDeposits account storedDepositWord
    let oldOwedDepositWord ← getMapping accountOwedDeposits account
    let newOwedDepositWord := add oldOwedDepositWord owedDepositDelta
    require (newOwedDepositWord < 79228162514264337593543950336)
      "BENCHMARK_ACCOUNT_OWED_NO_FIELD_OVERLAP_SCOPE"
    let storedOwedDepositWord := mul
      (mod (div newOwedDepositWord 4294967296) 18446744073709551616) 4294967296
    setMapping accountOwedDeposits account storedOwedDepositWord

  function internal _requireCfaOnlyAvailableNonnegative
      (account : Address, currentTimestamp : Uint256) : Unit := do
    _requireCanonicalAccount account
    let oldTimestamp ← getMapping accountTimestamps account
    let netFlowRateWord ← getMapping accountNetFlowRates account
    let settledWord ← getMapping sharedSettledBalances account
    let depositWord ← getMapping accountDeposits account
    let owedDepositWord ← getMapping accountOwedDeposits account
    require (owedDepositWord == 0) "CFA_ONLY_ZERO_OWED"
    require (currentTimestamp >= oldTimestamp) "CFA_AVAILABLE_TIMESTAMP"
    let dynamicWord := mul (sub currentTimestamp oldTimestamp) netFlowRateWord
    let rawWord := add settledWord dynamicWord
    let settledNonnegative := settledWord <
      57896044618658097711785492504343953926634992332820282019728792003956564819968
    let dynamicNonnegative := dynamicWord <
      57896044618658097711785492504343953926634992332820282019728792003956564819968
    let rawNonnegative := rawWord <
      57896044618658097711785492504343953926634992332820282019728792003956564819968
    if settledNonnegative == dynamicNonnegative then
      require (rawNonnegative == settledNonnegative) "CFA_AVAILABLE_RAW_OVERFLOW"
    else
      pure ()
    require (rawWord <
      57896044618658097711785492504343953926634992332820282019728792003956564819968)
      "CFA_NEGATIVE_RAW_BALANCE"
    let availableWord := sub rawWord depositWord
    require (availableWord <
      57896044618658097711785492504343953926634992332820282019728792003956564819968)
      "CFA_INSUFFICIENT_BALANCE"

  function internal _changeFlow
      (sender : Address, receiver : Address, newFlowRate : Uint256,
       newDeposit : Uint256, currentTimestamp : Uint256) : Unit := do
    let oldFlowRate ← getMapping2 flowRates sender receiver
    let oldFlowDeposit ← getMapping2 flowDeposits sender receiver
    let oldFlowOwedDeposit ← getMapping2 flowOwedDeposits sender receiver
    require (newDeposit < 79228162514264337593543950336)
      "BENCHMARK_FLOW_DEPOSIT_NO_FIELD_OVERLAP_SCOPE"
    let depositDeltaBase := sub newDeposit oldFlowDeposit
    let depositDelta := add depositDeltaBase oldFlowOwedDeposit
    let storedNewDeposit := mul
      (mod (div newDeposit 4294967296) 18446744073709551616) 4294967296
    if newFlowRate != 0 && newFlowRate <= 39614081257132168796771975167 then
      setMapping2 flowTimestamps sender receiver currentTimestamp
    else
      setMapping2 flowTimestamps sender receiver 0
    setMapping2 flowRates sender receiver newFlowRate
    setMapping2 flowDeposits sender receiver storedNewDeposit
    setMapping2 flowOwedDeposits sender receiver oldFlowOwedDeposit
    let senderFlowRateDelta := sub oldFlowRate newFlowRate
    let receiverFlowRateDelta := sub newFlowRate oldFlowRate
    _updateAccountFlowState sender senderFlowRateDelta depositDelta 0 currentTimestamp
    _updateAccountFlowState receiver receiverFlowRateDelta 0 0 currentTimestamp

  function createFlowNonApp
      (sender : Address, receiver : Address, newFlowRate : Uint256, liquidationPeriod : Uint256,
       minimumDeposit : Uint256, currentTimestamp : Uint256) : Unit := do
    require (receiver != 0) "CFA_ZERO_ADDRESS_RECEIVER"
    require (sender != receiver) "CFA_NO_SELF_FLOW"
    require (newFlowRate != 0 && newFlowRate <= 39614081257132168796771975167)
      "CFA_INVALID_FLOW_RATE"
    _requireSourceEnvironment sender receiver liquidationPeriod minimumDeposit
    _requireDirectOuterHostContext sender
    let senderIsApp ← getMapping hostIsApp sender
    let receiverIsApp ← getMapping hostIsApp receiver
    require (senderIsApp == 0) "CFA_SENDER_IS_APP"
    require (receiverIsApp == 0) "CFA_RECEIVER_IS_APP"
    _requireEmptyFlow sender receiver
    _requireCanonicalAccount sender
    _requireCanonicalAccount receiver
    let senderOwed ← getMapping accountOwedDeposits sender
    let receiverOwed ← getMapping accountOwedDeposits receiver
    require (senderOwed == 0) "CFA_ONLY_ZERO_SENDER_OWED"
    require (receiverOwed == 0) "CFA_ONLY_ZERO_RECEIVER_OWED"
    let newDeposit ← _calculateSourceDeposit newFlowRate liquidationPeriod minimumDeposit
    _changeFlow sender receiver newFlowRate newDeposit currentTimestamp
    setMapping2 flowExists sender receiver 1
    _requireCfaOnlyAvailableNonnegative sender currentTimestamp

  function updateFlowNonApp
      (sender : Address, receiver : Address, newFlowRate : Uint256, liquidationPeriod : Uint256,
       minimumDeposit : Uint256, currentTimestamp : Uint256) : Unit := do
    require (receiver != 0) "CFA_ZERO_ADDRESS_RECEIVER"
    require (sender != receiver) "CFA_NO_SELF_FLOW"
    require (newFlowRate != 0 && newFlowRate <= 39614081257132168796771975167)
      "CFA_INVALID_FLOW_RATE"
    _requireSourceEnvironment sender receiver liquidationPeriod minimumDeposit
    _requireDirectOuterHostContext sender
    let senderIsApp ← getMapping hostIsApp sender
    let receiverIsApp ← getMapping hostIsApp receiver
    require (senderIsApp == 0) "CFA_SENDER_IS_APP"
    require (receiverIsApp == 0) "CFA_RECEIVER_IS_APP"
    _requireExistingZeroOwedFlow sender receiver
    _requireCanonicalAccount sender
    _requireCanonicalAccount receiver
    let senderOwed ← getMapping accountOwedDeposits sender
    let receiverOwed ← getMapping accountOwedDeposits receiver
    require (senderOwed == 0) "CFA_ONLY_ZERO_SENDER_OWED"
    require (receiverOwed == 0) "CFA_ONLY_ZERO_RECEIVER_OWED"
    let newDeposit ← _calculateSourceDeposit newFlowRate liquidationPeriod minimumDeposit
    _changeFlow sender receiver newFlowRate newDeposit currentTimestamp
    _requireCfaOnlyAvailableNonnegative sender currentTimestamp

  function deleteFlowNonAppBySender
      (sender : Address, receiver : Address, currentTimestamp : Uint256) : Unit := do
    require (sender != 0) "CFA_ZERO_ADDRESS_SENDER"
    require (receiver != 0) "CFA_ZERO_ADDRESS_RECEIVER"
    let configuredLiquidationPeriod ← getStorage governanceLiquidationPeriod
    let configuredMinimumDeposit ← getStorage governanceMinimumDeposit
    _requireSourceEnvironment sender receiver configuredLiquidationPeriod configuredMinimumDeposit
    _requireDirectOuterHostContext sender
    let senderIsApp ← getMapping hostIsApp sender
    let receiverIsApp ← getMapping hostIsApp receiver
    require (senderIsApp == 0) "CFA_SENDER_IS_APP"
    require (receiverIsApp == 0) "CFA_RECEIVER_IS_APP"
    _requireExistingZeroOwedFlow sender receiver
    _requireCanonicalAccount sender
    _requireCanonicalAccount receiver
    let senderOwed ← getMapping accountOwedDeposits sender
    let receiverOwed ← getMapping accountOwedDeposits receiver
    require (senderOwed == 0) "CFA_ONLY_ZERO_SENDER_OWED"
    require (receiverOwed == 0) "CFA_ONLY_ZERO_RECEIVER_OWED"
    _requireCfaOnlyAvailableNonnegative sender currentTimestamp
    _changeFlow sender receiver 0 0 currentTimestamp
    setMapping2 flowExists sender receiver 0
    _requireCfaOnlyAvailableNonnegative sender currentTimestamp

  -- Source-pinned checks and CREATE_FLOW writes before the enabled after-created callback.
  function internal _receiverDeleteCallbackOuterPrefix
      (sender : Address, receiver : Address, newFlowRate : Uint256, liquidationPeriod : Uint256,
       minimumDeposit : Uint256, currentTimestamp : Uint256) : Uint256 := do
    require (receiver != 0) "CFA_ZERO_ADDRESS_RECEIVER"
    require (sender != receiver) "CFA_NO_SELF_FLOW"
    require (newFlowRate != 0 && newFlowRate <= 39614081257132168796771975167)
      "CFA_INVALID_FLOW_RATE"
    _requireSourceEnvironment sender receiver liquidationPeriod minimumDeposit
    _requireDirectOuterHostContext sender
    let receiverIsApp ← getMapping hostIsApp receiver
    let senderIsApp ← getMapping hostIsApp sender
    let receiverIsJailed ← getMapping hostIsJailed receiver
    let beforeCreatedNoop ← getMapping hostBeforeCreatedNoop receiver
    let afterCreatedEnabled ← getMapping hostAfterCreatedEnabled receiver
    let callbackCreditUsed ← getMapping hostCallbackCreditUsed receiver
    let callbackLevel ← getMapping hostCallbackLevel receiver
    let callbackActor ← getMapping hostCallbackActor receiver
    let callbackAppAddress ← getMapping hostCallbackAppAddress receiver
    let isAppCallbackContext ← getMapping hostIsAppCallbackContext receiver
    let contextualDeleteEnabled ← getMapping hostContextualDeleteEnabled receiver
    let nestedCallbackSuppressed ← getMapping hostNestedCallbackSuppressed receiver
    let appCreditTokenMatches ← getMapping hostAppCreditTokenMatches receiver
    let appCreditGranted ← getMapping hostAppCreditGranted receiver
    let additionalAppCredit ← getMapping hostAdditionalAppCredit receiver
    let receiverIsSelfDeletingFlowApp ← getMapping hostIsSelfDeletingFlowApp receiver
    require (receiverIsApp == 1) "HOST_RECEIVER_NOT_APP"
    require (senderIsApp == 0) "HOST_SENDER_APP_BRANCH_UNMODELED"
    require (receiverIsJailed == 0) "HOST_RECEIVER_JAILED"
    require (beforeCreatedNoop == 1) "HOST_BEFORE_CREATED_NOT_NOOP"
    require (afterCreatedEnabled == 1) "HOST_AFTER_CREATED_DISABLED"
    require (callbackCreditUsed == 0) "HOST_CALLBACK_CREDIT_USED"
    require (callbackLevel == 1) "HOST_CALLBACK_LEVEL"
    require (callbackActor == receiver) "HOST_CALLBACK_ACTOR"
    require (callbackAppAddress == receiver) "HOST_CALLBACK_APP"
    require (isAppCallbackContext == 1) "HOST_CALLBACK_CALL_TYPE"
    require (contextualDeleteEnabled == 1) "HOST_CONTEXTUAL_DELETE"
    require (nestedCallbackSuppressed == 1) "HOST_NESTED_CALLBACK"
    require (appCreditTokenMatches == 1) "HOST_APP_CREDIT_TOKEN"
    require (receiverIsSelfDeletingFlowApp == 1) "HOST_RECEIVER_NOT_SELF_DELETING_FLOW_APP"
    _requireEmptyFlow sender receiver
    _requireCanonicalAccount sender
    _requireCanonicalAccount receiver
    let senderOwed ← getMapping accountOwedDeposits sender
    let receiverOwed ← getMapping accountOwedDeposits receiver
    require (senderOwed == 0) "CFA_ONLY_ZERO_SENDER_OWED"
    require (receiverOwed == 0) "CFA_ONLY_ZERO_RECEIVER_OWED"
    -- `_changeFlow` returns the clipped pre-minimum deposit as app-credit base.
    let appCreditBase ← _calculateSourceAppCreditBase newFlowRate liquidationPeriod
    let newDeposit ← _calculateSourceDeposit newFlowRate liquidationPeriod minimumDeposit
    if appCreditBase == 0 then
      require (additionalAppCredit == 0) "HOST_ADDITIONAL_APP_CREDIT_ZERO"
      require (appCreditGranted == 0) "HOST_APP_CREDIT_GRANTED_ZERO"
    else
      require (additionalAppCredit >= 4294967296) "HOST_ADDITIONAL_APP_CREDIT_DEFAULT"
      require (additionalAppCredit >= minimumDeposit) "HOST_ADDITIONAL_APP_CREDIT_MINIMUM"
      require (additionalAppCredit == 4294967296 || additionalAppCredit == minimumDeposit)
        "HOST_ADDITIONAL_APP_CREDIT_MAX"
      require (appCreditGranted == add appCreditBase additionalAppCredit)
        "HOST_APP_CREDIT_GRANTED"

    -- Outer CREATE_FLOW before callback (the before-created hook is configured NOOP).
    _changeFlow sender receiver newFlowRate newDeposit currentTimestamp
    setMapping2 flowExists sender receiver 1
    return newDeposit

  -- Level-1 `SelfDeletingFlowTestApp.afterAgreementCreated` contextual delete.
  -- The exact `(sender, receiver, timestamp)` parameters are supplied by the concrete runner.
  function internal _receiverDeleteCallbackNestedDelete
      (sender : Address, receiver : Address, currentTimestamp : Uint256) : Unit := do
    -- This selected receiver-initiated same-flow branch requests `appToCallback = 0`
    -- (CFA:551-564); that source fact is distinct from generic level-2 rejection.
    _requireCfaOnlyAvailableNonnegative sender currentTimestamp
    _requireExistingZeroOwedFlow sender receiver
    _changeFlow sender receiver 0 0 currentTimestamp
    setMapping2 flowExists sender receiver 0

  -- Outer `_changeFlowToApp` reload and zero-credit reconciliation after nested success.
  function internal _receiverDeleteCallbackOuterResume
      (sender : Address, receiver : Address, currentTimestamp : Uint256) : Uint256 := do
    let reloadedFlowRate ← getMapping2 flowRates sender receiver
    let reloadedFlowOwed ← getMapping2 flowOwedDeposits sender receiver
    require (reloadedFlowOwed == 0) "CFA_RELOADED_OWED_DEPOSIT"
    _updateAccountFlowState sender 0 0 0 currentTimestamp
    _updateAccountFlowState receiver 0 0 0 currentTimestamp
    _requireCfaOnlyAvailableNonnegative sender currentTimestamp
    _requireCfaOnlyAvailableNonnegative receiver currentTimestamp
    return reloadedFlowRate

/-!
The behavioral hook below abstracts only the selected callback stack discipline. It is
not a complete Host ABI/context-validation model; the concrete outer prefix above keeps
the actor/app/token/context, registry, noop, jailed, credit, and source guards.

The sequencing intentionally uses Verity `bind`: `.lake/packages/verity/Verity/Core.lean`
lines 291-295 skip a continuation after revert, while lines 296-301 make top-level
`Contract.run` restore the original pre-call state. Thus a nested revert cannot reach
`outerResume`, and the top-level result carries the pre-prefix state.
-/

/-- Execute the supplied callback program at the permitted level and reject every other
level before its program can execute. Public properties expose the required `level ≥ 2`
case; level zero is outside this pushed-callback abstraction. -/
def behavioralOneLevelCallback {α : Type} (level : Nat) (nested : Contract α) : Contract α :=
  if level = 1 then
    nested
  else
    Verity.bind (Verity.require false "HOST_CALLBACK_LEVEL_EXCEEDED") (fun _ => nested)

/-- Typed outer-prefix / level-1 nested call / outer-resume composition. -/
def runOneLevelOuterNested {α β γ : Type}
    (outerPrefix : Contract α)
    (nested : α → Contract β)
    (outerResume : α → β → Contract γ) : Contract γ := do
  let prefixValue ← outerPrefix
  let nestedValue ← behavioralOneLevelCallback 1 (nested prefixValue)
  outerResume prefixValue nestedValue

/-- Pinned create-only SelfDeletingFlowTestApp schedule, implemented through the
factored behavioral runner while retaining its existing public name and type. -/
def SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback
    (sender receiver : Address) (newFlowRate liquidationPeriod minimumDeposit
      currentTimestamp : Uint256) : Contract Uint256 :=
  runOneLevelOuterNested
    (SuperfluidCFA._receiverDeleteCallbackOuterPrefix sender receiver newFlowRate
      liquidationPeriod minimumDeposit currentTimestamp)
    (fun _ => SuperfluidCFA._receiverDeleteCallbackNestedDelete sender receiver currentTimestamp)
    (fun _ _ => SuperfluidCFA._receiverDeleteCallbackOuterResume sender receiver currentTimestamp)

/-- Executable regression: nested failure rolls the prefix write back and never exposes
the resume poison write. -/
def nestedFailureRollbackWitnessProgram : Contract Unit :=
  runOneLevelOuterNested
    (setStorage (⟨40⟩ : StorageSlot Uint256) 1)
    (fun _ => Verity.require false "NESTED_FAIL")
    (fun _ _ => setStorage (⟨40⟩ : StorageSlot Uint256) 2)

theorem nestedFailureRollbackWitness :
    nestedFailureRollbackWitnessProgram.run defaultState =
      ContractResult.revert "NESTED_FAIL" defaultState := by
  rfl

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
