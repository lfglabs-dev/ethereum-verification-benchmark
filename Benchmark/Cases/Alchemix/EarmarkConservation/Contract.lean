import Contracts.Common

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Verity model of the Alchemix V3 earmarking accounting system.

  Upstream: alchemix-finance/v3 (master)
  Commit:   117c95b6ee11a75221d6fbdc79f16ac6acdb96f5
  File:     src/AlchemistV3.sol
  In scope: _earmark, _sync, _computeUnrealizedAccount, redeem,
            _subEarmarkedDebt, _subDebt

  Naming convention used in this file
  ------------------------------------
  - Function names mirror the Solidity source: `_earmark`, `_sync`,
    `_subEarmarkedDebt`, `_subDebt` keep their leading underscore,
    `redeem` does not (matches Solidity visibility).
  - Storage slot names mirror the Solidity source variable names. Private
    state variables keep their leading underscore (`_earmarkWeight`,
    `_redemptionWeight`, `_survivalAccumulator`); public state variables
    do not (`cumulativeEarmarked`, `totalDebt`).
  - Loaded local copies of slots take a trailing underscore: `let
    cumulativeEarmarked_ ← getStorage cumulativeEarmarked` reads the value
    at the slot named `cumulativeEarmarked` into a local called
    `cumulativeEarmarked_`. The Lean parser cannot reuse the same
    identifier for both, so the trailing-underscore form is the standard
    Verity convention (see Lido VaulthubLocked, Wildcat BorrowLiquiditySafety).
  - The `mapping(uint256 => Account)` struct is flattened: each Account
    field becomes its own slot, `_accounts[id].debt` becomes
    `_accounts_debt[id]`, etc. Verity has no struct mapping primitive.

  The benchmark targets the lazy-projected earmark conservation invariant
  agreed with the Alchemix team (Ov3rkoalafied, 2026-04-24):

      Sum over active accounts of project(account, _earmarkWeight,
        _redemptionWeight, _survivalAccumulator).newEarmarked
        = cumulativeEarmarked

  where `project = _computeUnrealizedAccount`. The literal "sum of stored
  account.earmarked equals cumulativeEarmarked" is provably false on the
  deployed code (see source comment line 1014: "Global can lag local by
  rounding") because per-account earmarked is updated lazily inside
  _sync(tokenId), not eagerly by _earmark. The lazy-projected version is
  the property the design actually maintains.

  Simplifications
  ----------------
  What was simplified:
  - `mulQ128(a, b)` and `divQ128(a, b)` are modeled as `mulDivDown` against
    `2^128` and treated as exact (no floor-rounding drift) for the purposes
    of the conservation invariant.
  Why:
  - The deployed code uses floor-rounding Q128.128 fixed-point arithmetic,
    so the literal per-step sum can drift from `cumulativeEarmarked` by
    bounded ulp errors. The team confirmed they care about the design-level
    conservation property, not a bounded-drift bound. We absorb the rounding
    into an explicit linearity assumption surfaced in `Specs.lean` and the
    case-study article. A follow-up case can sharpen this into a quantitative
    bounded-drift theorem.

  What was simplified:
  - The set of active token IDs is passed as an explicit
    `activeIds : FiniteSet Uint256` rather than a ghost field of
    `ContractState`.
  Why:
  - `Verity.Core.ContractState` exposes `knownAddresses : Nat -> FiniteAddressSet`
    for `mapping(address => T)` cases (used by `Verity.Specs.Common.Sum.sumBalances`)
    but has no parallel `knownTokenIds : Nat -> FiniteSet Uint256` for
    `mapping(uint256 => T)` cases. Verity-gap, surfaced as a proposed issue.
    Workaround is purely spec-level: pass the finset explicitly.

  What was simplified:
  - The cross-epoch branch of `_computeUnrealizedAccount` (source lines
    1539-1564: when the earmark epoch advances between an account's last
    sync and now, the projection splits at the boundary using the
    `_earmarkEpochStartRedemptionWeight` / `_earmarkEpochStartSurvivalAccumulator`
    snapshot mappings) is folded into the same-epoch path.
  Why:
  - This first-pass case targets the within-epoch conservation property,
    which is the dominant operational regime. The cross-epoch reconciliation
    logic is correctness-preserving but adds substantial proof surface.

  What was simplified:
  - The default same-epoch sub-branch of `_computeUnrealizedAccount`
    (source line 1517: `earmarkedUnredeemed = mulQ128(userExposure,
    unredeemedRatio)` via `_survivalAccumulator` diff) is collapsed into
    the telescoped same-epoch sub-branch (source line 1530:
    `earmarkedUnredeemed = mulQ128(earmarkRaw, survivalRatio)`).
  Why:
  - Under Q128 idealization the two branches coincide algebraically.

  What was simplified:
  - The `if (newEarmarked > newDebt) newEarmarked = newDebt;` cap (source
    lines 1503 and 1578) is omitted from the projection.
  Why:
  - Under the conservation invariant pre-state and Q128 idealization, the
    cap is provably a no-op (one of the side-properties carried by the
    invariant is `account.earmarked ≤ account.debt`).

  What was simplified:
  - When `redeem(amount)` is called with `amount == liveEarmarked` (full
    wipe), the source advances the redemption epoch and resets the index
    via `_packRed(oldEpoch + 1, ONE_Q128)`. The model writes
    `redemptionWeight := mulQ128(redemptionWeight, 0) = 0` instead.
  Why:
  - The model treats `_redemptionWeight` as a flat Q128 weight, not a
    packed (epoch, index) pair. Both representations yield the same
    survival ratio on the proved within-epoch paths when the active
    account snapshots are non-zero. Zero snapshots are excluded by an
    explicit model-artifact hypothesis until the packed epoch/index
    representation is modeled directly.

  What was simplified:
  - Early-returns and conditional state writes are encoded with pure `ite`
    over the new value (writing the unchanged value back) rather than
    monadic if/else.
  Why:
  - Multi-branch monadic if/else with reads is brittle inside
    `verity_contract` bodies. Keeping all writes unconditional with
    `ite`-computed new values preserves semantics and matches the pattern
    used in Wildcat BorrowLiquiditySafety.

  What was simplified:
  - The pre-amble of `_earmark()` (source lines 1583-1609: block-number
    guard, transmuter MYT balance read, `_pendingCoverShares` update,
    `Transmuter.queryGraph` external call, cover-shares application) is
    abstracted into a single ghost storage slot `_transmuterEarmarkAmount`.
    The Verity `_earmark` function reads that slot directly as `amount`.
  Why:
  - Cover-shares logic only feeds *how much* gets earmarked this window;
    it does not affect *whether* per-account earmarked sums to
    `cumulativeEarmarked`. The conservation invariant holds for any value
    of `amount` between 0 and `liveUnearmarked`. Modeling the pre-amble
    line-by-line would inflate the model and the proof without changing
    the invariant proof obligation.

  What was simplified:
  - External calls (`ITransmuter(transmuter).queryGraph(...)`,
    `TokenUtils.safeBalanceOf(myt, transmuter)`, `TokenUtils.safeTransfer`)
    are modeled as opaque ghost storage reads / no-ops.
  Why:
  - Standard benchmark practice. Internal accounting only.

  What was simplified:
  - `Account` fields not relevant to the invariant (`collateralBalance`,
    `freeCollateral`, `lastCollateralWeight`, `lastMintBlock`,
    `lastRepayBlock`, `lastTotalRedeemedDebt`, `lastTotalRedeemedSharesOut`,
    `mintAllowances`, `allowancesVersion`) are dropped from the model.
  Why:
  - Of the 13 fields in the source `Account` struct, only 5 are read or
    written along paths that affect `cumulativeEarmarked` or
    `account.earmarked`: `debt`, `earmarked`, `lastAccruedEarmarkWeight`,
    `lastAccruedRedemptionWeight`, `lastSurvivalAccumulator`.

  What was simplified:
  - Modifiers (`onlyTransmuter`, `onlyAdmin`, etc.), `Initializable`,
    NFT ownership checks, and pause flags are dropped.
  Why:
  - These constrain who can call, not how state evolves. Irrelevant
    to the conservation property.
-/

/-! ## Constants and Q128 helpers -/

/-- Q128 unit: `2^128`. Source: `AlchemistV3.sol:24` (`uint256(1) << 128`).
    Inlined as the literal `340282366920938463463374607431768211456` in
    `verity_contract` bodies because the macro does not see top-level
    `def`s (see verity issue #1749). The named def is kept here for
    `Specs.lean` and `Proofs.lean`. -/
def ONE_Q128 : Uint256 := 340282366920938463463374607431768211456

/-- `mulQ128(a, b) = floor(a * b / 2^128)`. Treated as exact under the
    Q128-idealization assumption (see `Specs.lean`).

    Source: `FixedPointMath.mulQ128`. -/
def mulQ128 (a b : Uint256) : Uint256 := div (mul a b) ONE_Q128

/-- `divQ128(a, b) = floor(a * 2^128 / b)`.

    Source: `FixedPointMath.divQ128`. -/
def divQ128 (a b : Uint256) : Uint256 := div (mul a ONE_Q128) b

/-! ## Storage layout

  The model preserves Solidity slot names where possible. Private state
  variables in Solidity (those declared `private` or with leading `_`)
  retain a leading underscore. Struct-of-mappings is flattened: each
  Account field becomes its own slot keyed by tokenId.
-/

verity_contract AlchemistV3 where
  storage
    /- Models `uint256 public cumulativeEarmarked;` (AlchemistV3.sol:45).
       Total earmarked debt across all accounts. -/
    cumulativeEarmarked : Uint256 := slot 0

    /- Models `uint256 public totalDebt;` (AlchemistV3.sol:72).
       Sum of all account debt. -/
    totalDebt : Uint256 := slot 1

    /- Models `uint256 private _earmarkWeight;` (AlchemistV3.sol:120).
       Q128 packed weight tracking how much live unearmarked debt survives
       each earmark step. -/
    _earmarkWeight : Uint256 := slot 2

    /- Models `uint256 private _redemptionWeight;` (AlchemistV3.sol:123).
       Q128 packed weight tracking survival of earmarked debt across
       redemptions. -/
    _redemptionWeight : Uint256 := slot 3

    /- Models `uint256 private _survivalAccumulator;` (AlchemistV3.sol:126).
       Accumulator used to reconstruct earmarked debt survival across
       redemption windows. -/
    _survivalAccumulator : Uint256 := slot 4

    /- Ghost slot — abstracts the pre-amble of `_earmark()`
       (AlchemistV3.sol:1583-1609: transmuter query + cover shares).
       Read directly as the net `amount` to be earmarked this window.
       See simplifications block. -/
    _transmuterEarmarkAmount : Uint256 := slot 5

    /- Models `_accounts[tokenId].debt`. The Solidity Account struct
       (AlchemistV3.sol Account, IAlchemistV3State) is flattened: each
       field becomes its own `mapping(uint256 => uint256)`. -/
    _accounts_debt : Uint256 → Uint256 := slot 100

    /- Models `_accounts[tokenId].earmarked`. -/
    _accounts_earmarked : Uint256 → Uint256 := slot 101

    /- Models `_accounts[tokenId].lastAccruedEarmarkWeight`. -/
    _accounts_lastAccruedEarmarkWeight : Uint256 → Uint256 := slot 102

    /- Models `_accounts[tokenId].lastAccruedRedemptionWeight`. -/
    _accounts_lastAccruedRedemptionWeight : Uint256 → Uint256 := slot 103

    /- Models `_accounts[tokenId].lastSurvivalAccumulator`. -/
    _accounts_lastSurvivalAccumulator : Uint256 → Uint256 := slot 104

  /-
    Models `_earmark()` (AlchemistV3.sol:1582-1641), within-epoch path
    only. The pre-amble (lines 1583-1609) is abstracted into a single
    `_transmuterEarmarkAmount` ghost read.

    Solidity (the part we model, lines 1610-1640):
      uint256 amount = transmuterEarmarkAmount;       // ghost-read
      uint256 liveUnearmarked = totalDebt - cumulativeEarmarked;
      if (amount > liveUnearmarked) amount = liveUnearmarked;
      if (amount > 0 && liveUnearmarked != 0) {
        uint256 ratioWanted = (amount == liveUnearmarked) ? 0
          : divQ128(liveUnearmarked - amount, liveUnearmarked);
        // _simulateEarmarkPackedUpdate (within-epoch): ratioApplied = ratioWanted
        uint256 ratioApplied = ratioWanted;
        uint256 oldEarmarkWeight = _earmarkWeight;
        _earmarkWeight = mulQ128(oldEarmarkWeight, ratioApplied);
        uint256 earmarkedFraction = ONE_Q128 - ratioApplied;
        _survivalAccumulator += mulQ128(oldEarmarkWeight, earmarkedFraction);
        uint256 newUnearmarked = mulQ128(liveUnearmarked, ratioApplied);
        uint256 effectiveEarmarked = liveUnearmarked - newUnearmarked;
        cumulativeEarmarked += effectiveEarmarked;
      }
  -/
  function _earmark () : Unit := do
    -- src: AlchemistV3.sol:1583-1609 — transmuter query + cover shares (abstracted)
    let totalDebt_ ← getStorage totalDebt
    let cumulativeEarmarked_ ← getStorage cumulativeEarmarked
    let earmarkWeight_ ← getStorage _earmarkWeight
    let survivalAccumulator_ ← getStorage _survivalAccumulator
    let amountIn ← getStorage _transmuterEarmarkAmount

    -- src: AlchemistV3.sol:1610-1611 — liveUnearmarked, cap amount
    let liveUnearmarked := sub totalDebt_ cumulativeEarmarked_
    let amount := ite (amountIn > liveUnearmarked) liveUnearmarked amountIn

    -- src: AlchemistV3.sol:1614-1616 — ratioWanted = (amount == liveUnearmarked) ? 0 : divQ128(...)
    -- Within-epoch: ratioApplied = ratioWanted, inline divQ128.
    let ratioWantedRaw := div (mul (sub liveUnearmarked amount) 340282366920938463463374607431768211456) liveUnearmarked
    let ratioApplied := ite (amount == liveUnearmarked) 0 ratioWantedRaw

    -- src: AlchemistV3.sol:1583+1613 — active gate: totalDebt != 0 AND amount > 0 AND liveUnearmarked != 0
    let active := totalDebt_ != 0 && amount != 0 && liveUnearmarked != 0

    -- src: AlchemistV3.sol:1622 — _earmarkWeight = mulQ128(oldEarmarkWeight, ratioApplied)
    let packedNew := div (mul earmarkWeight_ ratioApplied) 340282366920938463463374607431768211456
    let newEarmarkWeight := ite active packedNew earmarkWeight_

    -- src: AlchemistV3.sol:1625-1626 — _survivalAccumulator += mulQ128(oldIndex, earmarkedFraction)
    let earmarkedFraction := sub 340282366920938463463374607431768211456 ratioApplied
    let survivalIncrement := div (mul earmarkWeight_ earmarkedFraction) 340282366920938463463374607431768211456
    let newSurvivalAccumulator :=
      ite active (add survivalAccumulator_ survivalIncrement) survivalAccumulator_

    -- src: AlchemistV3.sol:1634-1637 — effectiveEarmarked, cumulativeEarmarked += effectiveEarmarked
    let newUnearmarked := div (mul liveUnearmarked ratioApplied) 340282366920938463463374607431768211456
    let effectiveEarmarked := sub liveUnearmarked newUnearmarked
    let newCumulativeEarmarked :=
      ite active (add cumulativeEarmarked_ effectiveEarmarked) cumulativeEarmarked_

    setStorage _earmarkWeight newEarmarkWeight
    setStorage _survivalAccumulator newSurvivalAccumulator
    setStorage cumulativeEarmarked newCumulativeEarmarked

  /-
    Models `_sync(tokenId)` (AlchemistV3.sol:1442-1472), invariant-relevant
    fields only. The body inlines the within-epoch / within-survival-window
    path of `_computeUnrealizedAccount` (source lines 1478-1579).

    Solidity (_sync):
      Account storage account = _accounts[tokenId];
      (uint256 newDebt, uint256 newEarmarked, uint256 redeemedTotal) =
        _computeUnrealizedAccount(account, _earmarkWeight,
          _redemptionWeight, _survivalAccumulator);
      // [collateral debit logic — out of scope for invariant]
      account.earmarked = newEarmarked;
      account.debt = newDebt;
      account.lastAccruedEarmarkWeight = _earmarkWeight;
      account.lastAccruedRedemptionWeight = _redemptionWeight;
      account.lastSurvivalAccumulator = _survivalAccumulator;
  -/
  function _sync (tokenId : Uint256) : Unit := do
    let earmarkWeight_ ← getStorage _earmarkWeight
    let redemptionWeight_ ← getStorage _redemptionWeight
    let survivalAccumulator_ ← getStorage _survivalAccumulator

    let accountDebt_ ← getMappingUint _accounts_debt tokenId
    let accountEarmarked_ ← getMappingUint _accounts_earmarked tokenId
    let lastEW_ ← getMappingUint _accounts_lastAccruedEarmarkWeight tokenId
    let lastRW_ ← getMappingUint _accounts_lastAccruedRedemptionWeight tokenId

    -- src: AlchemistV3.sol:1747-1763 — _earmarkSurvivalRatio(lastEW, _earmarkWeight)
    let earmarkSurvivalQ := div (mul earmarkWeight_ 340282366920938463463374607431768211456) lastEW_
    let unearmarkSurvivalRatio :=
      ite (lastEW_ == earmarkWeight_) 340282366920938463463374607431768211456
        (ite (lastEW_ == 0) 340282366920938463463374607431768211456 earmarkSurvivalQ)

    -- src: AlchemistV3.sol:1768-1789 — _redemptionSurvivalRatio(lastRW, _redemptionWeight)
    let redemptionSurvivalQ := div (mul redemptionWeight_ 340282366920938463463374607431768211456) lastRW_
    let redemptionSurvivalRatio :=
      ite (lastRW_ == redemptionWeight_) 340282366920938463463374607431768211456
        (ite (lastRW_ == 0) 340282366920938463463374607431768211456 redemptionSurvivalQ)

    -- src: AlchemistV3.sol:1489 — userExposure = debt - earmarked
    let userExposure :=
      ite (accountDebt_ > accountEarmarked_) (sub accountDebt_ accountEarmarked_) 0

    -- src: AlchemistV3.sol:1494-1497 — unearmarkedRemaining, earmarkRaw
    let unearmarkedRemaining := div (mul userExposure unearmarkSurvivalRatio) 340282366920938463463374607431768211456
    let earmarkRaw := sub userExposure unearmarkedRemaining

    -- src: AlchemistV3.sol:1530+1577 — newEarmarked (telescoped same-epoch path)
    -- newEarmarked = mulQ128(account.earmarked + earmarkRaw, redemptionSurvivalRatio)
    let totalEarmarkedNow := add accountEarmarked_ earmarkRaw
    let newEarmarked := div (mul totalEarmarkedNow redemptionSurvivalRatio) 340282366920938463463374607431768211456

    -- src: AlchemistV3.sol:1573-1576 — redeemedTotal, newDebt
    let redeemedFromAccount := sub totalEarmarkedNow newEarmarked
    let newDebt :=
      ite (accountDebt_ >= redeemedFromAccount) (sub accountDebt_ redeemedFromAccount) 0

    -- src: AlchemistV3.sol:1463-1471 — write back to account fields
    setMappingUint _accounts_debt tokenId newDebt
    setMappingUint _accounts_earmarked tokenId newEarmarked
    setMappingUint _accounts_lastAccruedEarmarkWeight tokenId earmarkWeight_
    setMappingUint _accounts_lastAccruedRedemptionWeight tokenId redemptionWeight_
    setMappingUint _accounts_lastSurvivalAccumulator tokenId survivalAccumulator_

  /-
    Models `redeem(amount)` (AlchemistV3.sol:655-731), within-epoch path.
    Only the parts that affect `cumulativeEarmarked`, weights, and `totalDebt`.
    Source's `_earmark()` call at line 656, collateral transfer math at
    lines 712-727, fee transfer, and event emission are out of scope.

    Solidity (the part we model, lines 658-708):
      uint256 liveEarmarked = cumulativeEarmarked;
      if (amount > liveEarmarked) amount = liveEarmarked;
      if (liveEarmarked != 0 && amount != 0) {
        uint256 ratioWanted = (amount == liveEarmarked) ? 0
          : divQ128(liveEarmarked - amount, liveEarmarked);
        // _redemptionWeight packed update (within-epoch): ratioApplied = ratioWanted
        _redemptionWeight = mulQ128(_redemptionWeight, ratioApplied);
        _survivalAccumulator = mulQ128(_survivalAccumulator, ratioApplied);
        uint256 remainingEarmarked = mulQ128(liveEarmarked, ratioApplied);
        uint256 effectiveRedeemed = liveEarmarked - remainingEarmarked;
        cumulativeEarmarked = remainingEarmarked;
        totalDebt -= effectiveRedeemed;
      }
  -/
  function redeem (amount : Uint256) : Unit := do
    let cumulativeEarmarked_ ← getStorage cumulativeEarmarked
    let totalDebt_ ← getStorage totalDebt
    let redemptionWeight_ ← getStorage _redemptionWeight
    let survivalAccumulator_ ← getStorage _survivalAccumulator

    -- src: AlchemistV3.sol:658-659 — liveEarmarked, cap amount
    let liveEarmarked := cumulativeEarmarked_
    let amountClamped := ite (amount > liveEarmarked) liveEarmarked amount

    -- src: AlchemistV3.sol:664-665 — ratioWanted = (amount == liveEarmarked) ? 0 : divQ128(...)
    -- Within-epoch: ratioApplied = ratioWanted
    let ratioWantedRaw := div (mul (sub liveEarmarked amountClamped) 340282366920938463463374607431768211456) liveEarmarked
    let ratioApplied := ite (amountClamped == liveEarmarked) 0 ratioWantedRaw

    -- src: AlchemistV3.sol:663 — active gate: liveEarmarked != 0 AND amountClamped != 0
    let active := liveEarmarked != 0 && amountClamped != 0

    -- src: AlchemistV3.sol:693+700+703+707 — inline mulQ128 for each updated value
    let newRedemptionWeightActive := div (mul redemptionWeight_ ratioApplied) 340282366920938463463374607431768211456
    let newSurvivalAccumulatorActive := div (mul survivalAccumulator_ ratioApplied) 340282366920938463463374607431768211456
    let remainingEarmarked := div (mul liveEarmarked ratioApplied) 340282366920938463463374607431768211456
    let effectiveRedeemed := sub liveEarmarked remainingEarmarked

    -- src: AlchemistV3.sol:693+700+706+707 — write back; inactive branch leaves storage unchanged
    let newRedemptionWeight := ite active newRedemptionWeightActive redemptionWeight_
    let newSurvivalAccumulator := ite active newSurvivalAccumulatorActive survivalAccumulator_
    let newCumulativeEarmarked := ite active remainingEarmarked cumulativeEarmarked_
    let newTotalDebt := ite active (sub totalDebt_ effectiveRedeemed) totalDebt_

    setStorage _redemptionWeight newRedemptionWeight
    setStorage _survivalAccumulator newSurvivalAccumulator
    setStorage cumulativeEarmarked newCumulativeEarmarked
    setStorage totalDebt newTotalDebt

  /-
    Models `_subEarmarkedDebt(amountInDebtTokens, accountId)`
    (AlchemistV3.sol:1002-1019). The function returns `earmarkToRemove` in
    Solidity; we drop the return because no caller path uses it for the
    invariant.

    Solidity:
      uint256 debt = account.debt;
      uint256 earmarkedDebt = account.earmarked;
      uint256 credit = amountInDebtTokens > debt ? debt : amountInDebtTokens;
      uint256 earmarkToRemove = credit > earmarkedDebt ? earmarkedDebt : credit;
      account.earmarked = earmarkedDebt - earmarkToRemove;
      uint256 remove = earmarkToRemove > cumulativeEarmarked
                          ? cumulativeEarmarked : earmarkToRemove;
      cumulativeEarmarked -= remove;
  -/
  function _subEarmarkedDebt (amountInDebtTokens : Uint256, accountId : Uint256) : Unit := do
    let cumulativeEarmarked_ ← getStorage cumulativeEarmarked
    let debt_ ← getMappingUint _accounts_debt accountId
    let earmarkedDebt_ ← getMappingUint _accounts_earmarked accountId

    -- src: AlchemistV3.sol:1008-1009 — credit, earmarkToRemove
    let credit := ite (amountInDebtTokens > debt_) debt_ amountInDebtTokens
    let earmarkToRemove := ite (credit > earmarkedDebt_) earmarkedDebt_ credit

    -- src: AlchemistV3.sol:1012 — account.earmarked -= earmarkToRemove
    setMappingUint _accounts_earmarked accountId (sub earmarkedDebt_ earmarkToRemove)

    -- src: AlchemistV3.sol:1015-1016 — clamped global subtraction
    let remove := ite (earmarkToRemove > cumulativeEarmarked_)
                    cumulativeEarmarked_ earmarkToRemove
    setStorage cumulativeEarmarked (sub cumulativeEarmarked_ remove)

  /-
    Models `_subDebt(tokenId, amount)` (AlchemistV3.sol:1300-1309), focused
    on the cumulativeEarmarked clamp at line 1306.

    Solidity:
      account.debt -= amount;
      totalDebt -= amount;
      if (cumulativeEarmarked > totalDebt) {
        cumulativeEarmarked = totalDebt;
      }
  -/
  function _subDebt (tokenId : Uint256, amount : Uint256) : Unit := do
    let totalDebt_ ← getStorage totalDebt
    let cumulativeEarmarked_ ← getStorage cumulativeEarmarked
    let accountDebt_ ← getMappingUint _accounts_debt tokenId

    -- src: AlchemistV3.sol:1303-1304 — account.debt -= amount; totalDebt -= amount
    setMappingUint _accounts_debt tokenId (sub accountDebt_ amount)
    let newTotalDebt := sub totalDebt_ amount
    setStorage totalDebt newTotalDebt

    -- src: AlchemistV3.sol:1306-1308 — clamp cumulativeEarmarked to newTotalDebt
    let newCumulativeEarmarked :=
      ite (cumulativeEarmarked_ > newTotalDebt) newTotalDebt cumulativeEarmarked_
    setStorage cumulativeEarmarked newCumulativeEarmarked

end Benchmark.Cases.Alchemix.EarmarkConservation
