import Contracts.Common

namespace Benchmark.Cases.Balancer.ReClammSwapRounding

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Verity model of the Balancer ReClamm swap quote arithmetic.

  Upstream: balancer/reclamm
  Commit:   cff18033d401a61326a2d6c078507084cbdc864b
  Files:    contracts/lib/ReClammMath.sol
            contracts/ReClammPool.sol
  In scope: ReClammMath.computeOutGivenIn,
            ReClammMath.computeInGivenOut,
            ReClammPool.onSwap dispatch to those helpers.

  Naming convention used in this file
  ------------------------------------
  - Function names mirror the Solidity source: `computeOutGivenIn`,
    `computeInGivenOut`, and `onSwap`.
  - Local names mirror Solidity parameter names where possible. Loaded
    storage locals would take a trailing underscore, but this slice has no
    storage because ReClammMath is a pure library surface.

  Target invariant
  ----------------
  For a successful swap quote with the current virtual balances held fixed,
  applying the returned real-balance deltas must not decrease:

      L = (balanceA + virtualBalanceA) * (balanceB + virtualBalanceB)

  This is the proof-engineering form of "swaps never round in the trader's
  favor." It isolates the exact arithmetic surface that Certora I-01 exposed:
  a floor where an intended ceil can make the user receive too much or pay too
  little.

  Simplifications
  ----------------
  What was simplified:
  - `uint256[] memory balancesScaled18` is modeled as two scalar parameters,
    `balanceA` and `balanceB`.
  Why:
  - ReClamm is a fixed two-token pool. Verity can model mappings/storage arrays,
    but memory dynamic arrays are unnecessary proof surface for this invariant.
    The rewrite is syntax-only: `balancesScaled18[a]` maps to `balanceA`, and
    `balancesScaled18[b]` maps to `balanceB`.

  What was simplified:
  - `PoolSwapParams memory request` in `onSwap` is flattened into scalar
    parameters.
  Why:
  - The invariant needs only `kind`, `balancesScaled18`, token indexes,
    `amountGivenScaled18`, and the current virtual balances. Flattening avoids a
    struct-memory model without changing the swap arithmetic.

  What was simplified:
  - `_computeCurrentVirtualBalances`, `_setLastVirtualBalances`, and
    `_updateTimestamp` are not modeled in `onSwap`; current virtual balances are
    explicit inputs.
  Why:
  - Phase 2's agreed theorem treats the virtual balances selected for this swap
    as fixed during quote computation. The omitted path contains timestamp
    interpolation, price-ratio updates, `sqrt`, and `powDown`, which are separate
    from the rounding bug class targeted here.

  What was simplified:
  - Vault application of returned amounts to real balances is modeled in
    `Specs.lean`, not in `onSwap`.
  Why:
  - Balancer Vault owns the actual token accounting. `onSwap` returns the quote;
    the post-swap real balances are therefore a spec boundary.

  What was simplified:
  - `ReClammPool.onSwap` inlines the `computeOutGivenIn` /
    `computeInGivenOut` arithmetic instead of calling the modeled
    `ReClammMath` functions.
  Why:
  - Cross-`verity_contract` library calls are not the stable proof surface in
    this benchmark version. The inlined blocks preserve the Solidity dispatch
    branch and helper arithmetic while avoiding a macro/linking issue that is
    unrelated to the rounding invariant.

  What was simplified:
  - Solidity 0.8 checked-arithmetic overflow reverts are not encoded as
    `require`s in the contract body.
  Why:
  - Verity's `Uint256` arithmetic is EVM-style modular arithmetic. The generated
    theorem surfaces no-overflow hypotheses for the multiplication/addition
    operations needed to connect the executable model to mathematical products.

  What was simplified:
  - Solidity division-by-zero reverts are represented by explicit denominator
    `require`s before division.
  Why:
  - Verity's `div` is total. Adding these guards preserves Solidity successful
    path semantics and makes revert conditions explicit.
-/

/-- Token index constant for token A. Source: `ReClammMath.sol:48`. -/
def a : Uint256 := 0

/-- Token index constant for token B. Source: `ReClammMath.sol:49`. -/
def b : Uint256 := 1

/--
  `FixedPoint.mulDivUp(x, y, denominator)` specialized for this case:
  `ceil(x * y / denominator)`.

  Source: `ReClammMath.sol:229-233`, via Balancer `FixedPoint.mulDivUp`.
  The denominator nonzero check is explicit in the contract bodies because
  Verity division is total while Solidity division by zero reverts.
-/
def mulDivUp (x y denominator : Uint256) : Uint256 :=
  let numerator := mul x y
  if numerator == 0 then 0 else add (div (sub numerator 1) denominator) 1

verity_contract ReClammMath where
  storage

  function computeOutGivenIn
      (balanceA : Uint256, balanceB : Uint256,
       virtualBalanceA : Uint256, virtualBalanceB : Uint256,
       tokenInIndex : Uint256, tokenOutIndex : Uint256,
       amountInScaled18 : Uint256) : Uint256 := do
    -- src: ReClammMath.sol:165-167 — choose virtual balances by token side.
    let virtualBalanceTokenIn := ite (tokenInIndex == 0) virtualBalanceA virtualBalanceB
    let virtualBalanceTokenOut := ite (tokenInIndex == 0) virtualBalanceB virtualBalanceA

    -- src: ReClammMath.sol:169-171 — floor output amount.
    let balanceTokenOut := ite (tokenOutIndex == 0) balanceA balanceB
    let balanceTokenIn := ite (tokenInIndex == 0) balanceA balanceB
    let denominator := add (add balanceTokenIn virtualBalanceTokenIn) amountInScaled18
    require (denominator != 0) "DivisionByZero"
    let amountOutScaled18 :=
      div (mul (add balanceTokenOut virtualBalanceTokenOut) amountInScaled18) denominator

    -- src: ReClammMath.sol:173-174 — amount out cannot exceed real balance.
    require (amountOutScaled18 <= balanceTokenOut) "AmountOutGreaterThanBalance"
    return amountOutScaled18

  function computeInGivenOut
      (balanceA : Uint256, balanceB : Uint256,
       virtualBalanceA : Uint256, virtualBalanceB : Uint256,
       tokenInIndex : Uint256, tokenOutIndex : Uint256,
       amountOutScaled18 : Uint256) : Uint256 := do
    -- src: ReClammMath.sol:221-222 — amount out cannot exceed real balance.
    let balanceTokenOut := ite (tokenOutIndex == 0) balanceA balanceB
    require (amountOutScaled18 <= balanceTokenOut) "AmountOutGreaterThanBalance"

    -- src: ReClammMath.sol:224-226 — choose virtual balances by token side.
    let virtualBalanceTokenIn := ite (tokenInIndex == 0) virtualBalanceA virtualBalanceB
    let virtualBalanceTokenOut := ite (tokenInIndex == 0) virtualBalanceB virtualBalanceA
    let balanceTokenIn := ite (tokenInIndex == 0) balanceA balanceB

    -- src: ReClammMath.sol:228-233 — ceil input amount via FixedPoint.mulDivUp.
    let denominator := sub (add balanceTokenOut virtualBalanceTokenOut) amountOutScaled18
    require (denominator != 0) "DivisionByZero"
    let amountInScaled18 :=
      mulDivUp (add balanceTokenIn virtualBalanceTokenIn) amountOutScaled18 denominator
    return amountInScaled18

verity_contract ReClammPool where
  storage

  function onSwap
      (exactIn : Bool,
       balanceA : Uint256, balanceB : Uint256,
       currentVirtualBalanceA : Uint256, currentVirtualBalanceB : Uint256,
       indexIn : Uint256, indexOut : Uint256,
       amountGivenScaled18 : Uint256) : Uint256 := do
    -- src: ReClammPool.sol:183-190 — current VBs already computed (abstracted input).
    -- src: ReClammPool.sol:192 — timestamp update omitted (see simplifications block).

    -- src: ReClammPool.sol:194-213 — dispatch by SwapKind.
    if exactIn then
      -- src: ReClammPool.sol:195-203 — EXACT_IN calls computeOutGivenIn.
      let virtualBalanceTokenIn := ite (indexIn == 0) currentVirtualBalanceA currentVirtualBalanceB
      let virtualBalanceTokenOut := ite (indexIn == 0) currentVirtualBalanceB currentVirtualBalanceA
      let balanceTokenOut := ite (indexOut == 0) balanceA balanceB
      let balanceTokenIn := ite (indexIn == 0) balanceA balanceB
      let denominator := add (add balanceTokenIn virtualBalanceTokenIn) amountGivenScaled18
      require (denominator != 0) "DivisionByZero"
      let amountCalculatedScaled18 :=
        div (mul (add balanceTokenOut virtualBalanceTokenOut) amountGivenScaled18) denominator
      require (amountCalculatedScaled18 <= balanceTokenOut) "AmountOutGreaterThanBalance"
      return amountCalculatedScaled18
    else
      -- src: ReClammPool.sol:204-212 — EXACT_OUT calls computeInGivenOut.
      let balanceTokenOut := ite (indexOut == 0) balanceA balanceB
      require (amountGivenScaled18 <= balanceTokenOut) "AmountOutGreaterThanBalance"
      let virtualBalanceTokenIn := ite (indexIn == 0) currentVirtualBalanceA currentVirtualBalanceB
      let virtualBalanceTokenOut := ite (indexIn == 0) currentVirtualBalanceB currentVirtualBalanceA
      let balanceTokenIn := ite (indexIn == 0) balanceA balanceB
      let denominator := sub (add balanceTokenOut virtualBalanceTokenOut) amountGivenScaled18
      require (denominator != 0) "DivisionByZero"
      let amountCalculatedScaled18 :=
        mulDivUp (add balanceTokenIn virtualBalanceTokenIn) amountGivenScaled18 denominator
      return amountCalculatedScaled18

end Benchmark.Cases.Balancer.ReClammSwapRounding
