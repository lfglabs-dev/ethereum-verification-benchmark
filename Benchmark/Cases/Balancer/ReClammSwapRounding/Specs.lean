import Verity.Specs.Common
import Benchmark.Cases.Balancer.ReClammSwapRounding.Contract

namespace Benchmark.Cases.Balancer.ReClammSwapRounding

open Verity
open Verity.EVM.Uint256

/-- Scalar replacement for `balancesScaled18[tokenIndex]`. -/
def balanceOf (tokenIndex balanceA balanceB : Uint256) : Uint256 :=
  if tokenIndex == 0 then balanceA else balanceB

/-- Scalar replacement for token-indexed virtual balances. -/
def virtualBalanceOf (tokenIndex virtualBalanceA virtualBalanceB : Uint256) : Uint256 :=
  if tokenIndex == 0 then virtualBalanceA else virtualBalanceB

/-- Mathematical, non-modular total balance for one token side. -/
def totalNat (balance virtualBalance : Uint256) : Nat :=
  balance.val + virtualBalance.val

/--
  Mathematical product before the quote is applied:
  `L_before = (Ra + Va) * (Rb + Vb)`.

  Uses Nat arithmetic so the invariant states the economic product rather than
  wrapped EVM arithmetic.
-/
def L_before
    (balanceA balanceB virtualBalanceA virtualBalanceB : Uint256) : Nat :=
  totalNat balanceA virtualBalanceA * totalNat balanceB virtualBalanceB

/-- Post-swap token-A real balance after applying the Vault-side deltas. -/
def postBalanceA
    (exactIn : Bool)
    (balanceA _balanceB : Uint256)
    (indexIn indexOut amountGivenScaled18 amountCalculatedScaled18 : Uint256) : Nat :=
  if exactIn then
    if indexIn == 0 then balanceA.val + amountGivenScaled18.val
    else if indexOut == 0 then balanceA.val - amountCalculatedScaled18.val
    else balanceA.val
  else
    if indexIn == 0 then balanceA.val + amountCalculatedScaled18.val
    else if indexOut == 0 then balanceA.val - amountGivenScaled18.val
    else balanceA.val

/-- Post-swap token-B real balance after applying the Vault-side deltas. -/
def postBalanceB
    (exactIn : Bool)
    (_balanceA balanceB : Uint256)
    (indexIn indexOut amountGivenScaled18 amountCalculatedScaled18 : Uint256) : Nat :=
  if exactIn then
    if indexIn == 1 then balanceB.val + amountGivenScaled18.val
    else if indexOut == 1 then balanceB.val - amountCalculatedScaled18.val
    else balanceB.val
  else
    if indexIn == 1 then balanceB.val + amountCalculatedScaled18.val
    else if indexOut == 1 then balanceB.val - amountGivenScaled18.val
    else balanceB.val

/-- Mathematical product after applying Vault-side real-balance deltas. -/
def L_after
    (exactIn : Bool)
    (balanceA balanceB virtualBalanceA virtualBalanceB : Uint256)
    (indexIn indexOut amountGivenScaled18 amountCalculatedScaled18 : Uint256) : Nat :=
  (postBalanceA exactIn balanceA balanceB indexIn indexOut amountGivenScaled18 amountCalculatedScaled18
      + virtualBalanceA.val) *
    (postBalanceB exactIn balanceA balanceB indexIn indexOut amountGivenScaled18 amountCalculatedScaled18
      + virtualBalanceB.val)

/--
  Bundles the Solidity 0.8 checked-arithmetic facts needed to read the
  executable `Uint256` quote as ordinary Nat arithmetic on the successful path.
-/
def onSwap_no_overflow_assumptions
    (exactIn : Bool)
    (balanceA balanceB virtualBalanceA virtualBalanceB : Uint256)
    (indexIn indexOut amountGivenScaled18 : Uint256) : Prop :=
  balanceA.val + virtualBalanceA.val < modulus ∧
  balanceB.val + virtualBalanceB.val < modulus ∧
  (if exactIn then
    (balanceOf indexIn balanceA balanceB).val +
          (virtualBalanceOf indexIn virtualBalanceA virtualBalanceB).val +
          amountGivenScaled18.val < modulus
   else True) ∧
  (if exactIn then
    ((balanceOf indexOut balanceA balanceB).val +
        (virtualBalanceOf indexOut virtualBalanceA virtualBalanceB).val) *
      amountGivenScaled18.val < modulus
   else True) ∧
  (if exactIn then True
   else
    ((balanceOf indexIn balanceA balanceB).val +
        (virtualBalanceOf indexIn virtualBalanceA virtualBalanceB).val) *
      amountGivenScaled18.val < modulus)

/--
  A successful `onSwap` quote, with current virtual balances held fixed, must
  not decrease the ReClamm product after the Vault applies the returned deltas.
-/
def onSwap_fixed_virtual_balances_product_non_decreasing_spec
    (exactIn : Bool)
    (balanceA balanceB virtualBalanceA virtualBalanceB : Uint256)
    (indexIn indexOut amountGivenScaled18 amountCalculatedScaled18 : Uint256) : Prop :=
  L_after exactIn balanceA balanceB virtualBalanceA virtualBalanceB
      indexIn indexOut amountGivenScaled18 amountCalculatedScaled18
    >= L_before balanceA balanceB virtualBalanceA virtualBalanceB

end Benchmark.Cases.Balancer.ReClammSwapRounding
