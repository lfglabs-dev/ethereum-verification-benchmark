import Contracts.Common

namespace Benchmark.Cases.Olas.V3DeadDeviationGuard

/-
  Focused model of Code4rena 2026-01 Olas H-02.

  On the successful-oracle path, `checkPoolAndGetCenterPrice` overwrites its named
  return variable, which previously held the spot sqrt price, with the TWAP sqrt
  price. It then recomputes `instantPrice` from that overwritten value. Since the
  oracle returned `twapPrice` from the same TWAP sqrt value, both prices are equal
  and deviation is always zero.

  `mulDiv(x, x, 2^64)` is represented by exact natural-number multiplication and
  division. This matches the mathematical relation relevant to the overwrite;
  pool calls, ABI encoding, early returns, and FullMath's 512-bit implementation
  are outside this normal-success-path slice.
-/

def priceFromSqrt (sqrtPriceX96 : Nat) : Nat :=
  (sqrtPriceX96 * sqrtPriceX96) / (2 ^ 64)

def priceDeviation (instantPrice twapPrice : Nat) : Nat :=
  if twapPrice = 0 then 0
  else if instantPrice > twapPrice then
    ((instantPrice - twapPrice) * (10 ^ 18)) / twapPrice
  else
    ((twapPrice - instantPrice) * (10 ^ 18)) / twapPrice

structure NormalPathResult where
  returnedCenterSqrtPriceX96 : Nat
  twapPrice : Nat
  instantPrice : Nat
  deviation : Nat
  deriving Repr, DecidableEq

/-- Source normal path. `spotSqrtPriceX96` is read, then lost to the overwrite. -/
def sourceNormalPath (_spotSqrtPriceX96 twapSqrtPriceX96 : Nat) : NormalPathResult :=
  let twapPrice := priceFromSqrt twapSqrtPriceX96
  let centerSqrtPriceX96 := twapSqrtPriceX96
  let instantPrice := priceFromSqrt centerSqrtPriceX96
  { returnedCenterSqrtPriceX96 := centerSqrtPriceX96
    twapPrice := twapPrice
    instantPrice := instantPrice
    deviation := priceDeviation instantPrice twapPrice }

end Benchmark.Cases.Olas.V3DeadDeviationGuard
