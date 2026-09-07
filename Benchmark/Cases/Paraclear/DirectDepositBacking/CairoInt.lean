import Mathlib

/-!
# Cairo integer and decimal helpers used by the Paraclear deposit model

The real contract stores internal amounts at eight decimals. ERC20 balances stay in
their native decimal precision. These definitions reproduce the three source branches:
equal precision, fewer token decimals, and more token decimals.
-/

namespace Benchmark.Cases.Paraclear.DirectDepositBacking

def paraclearDecimals : Nat := 8

def i128Min : Int := -(2 ^ 127)
def i128Max : Int := 2 ^ 127 - 1
def i128MaxNat : Nat := 2 ^ 127 - 1
def u256Max : Nat := 2 ^ 256 - 1

def inI128 (value : Int) : Bool :=
  decide (i128Min ≤ value ∧ value ≤ i128Max)

def scaleFactor (tokenDecimals : Nat) : Nat :=
  if tokenDecimals < paraclearDecimals then
    10 ^ (paraclearDecimals - tokenDecimals)
  else
    10 ^ (tokenDecimals - paraclearDecimals)

/-- Cairo `_scale_from_paraclear_decimals` on a validated nonnegative amount. -/
def toRaw (amount8 tokenDecimals : Nat) : Nat :=
  if tokenDecimals = paraclearDecimals then
    amount8
  else if tokenDecimals < paraclearDecimals then
    amount8 / scaleFactor tokenDecimals
  else
    amount8 * scaleFactor tokenDecimals

/-- Cairo `_scale_to_paraclear_decimals` on a nonnegative raw token amount. -/
def toInternal (rawAmount tokenDecimals : Nat) : Nat :=
  if tokenDecimals = paraclearDecimals then
    rawAmount
  else if tokenDecimals < paraclearDecimals then
    rawAmount * scaleFactor tokenDecimals
  else
    rawAmount / scaleFactor tokenDecimals

/-- The actual internal credit: convert to raw token units, then back to 8 decimals. -/
def depositCredit (amount8 tokenDecimals : Nat) : Nat :=
  toInternal (toRaw amount8 tokenDecimals) tokenDecimals

end Benchmark.Cases.Paraclear.DirectDepositBacking
