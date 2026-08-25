import Contracts.Common

namespace Benchmark.Cases.Doppler.MulticurveFeeConservation

/-!
# FullRangeFeeRehype accounting model

Source: `whetstoneresearch/damm` at
`6424187967f93df1185f435f3adbcac0ce8fc7ec`.
Target: `src/supported/grid-full-range/FullRangeFeeRehype.sol`.
Register match: `INV-REH-1 — Reservations are complete and covered`.

## Simplifications

* Solidity `uint128`/`uint256` amounts are modeled as `Nat`. The real contract
  uses checked casts, checked additions/subtractions, and reverts on overflow or
  underflow. Each modeled transition takes the corresponding ordering/equality
  preconditions, so the successful arithmetic branch is exact and unbounded.
* One registered market and its two token denominations are modeled directly.
  `otherReservedX/otherReservedY` summarize the unchanged carry reservations of
  every other registered market sharing those tokens. This keeps INV-REH-1's
  manager-credit coverage check global rather than incorrectly inferring a
  token-wide bound from one market's pointwise bound.
* DAMM calls are represented by their successful returned `spent`, `received`,
  and provided amounts. Reverting swap/provide legs are the identity/deferred
  transition, matching the Solidity `try/catch` behavior. Price execution is
  intentionally out of scope; the contract itself states that it guarantees
  credit accounting, not execution price.
* `originX/originY`, `paidX/paidY`, and `compoundedX/compoundedY` are proof-only
  ghost counters. Solidity stores carry and `reservedCredit`, while DAMM's
  credit ledger and beneficiary/LP balances hold the other sides. The ghosts
  expose the conservation equation without changing control flow.
* `managerCreditX/managerCreditY` model `DAMM.balanceOf(address(this), tokenId)`
  at settled function boundaries. Successful swaps re-denominate manager
  credit, transfers/provides debit it, and callbacks deposit into it. This
  makes INV-REH-1's coverage half explicit rather than assuming it.
* Beneficiary iteration is collapsed to its aggregate. The final beneficiary
  absorbs division residue, so `_distributeForwardsForToken` transfers exactly
  the aggregate forwarded amount on every successful call.

The model preserves source function/helper boundaries for the scoped accounting
transitions: `_onSwapFeeReceived`, `processFees`' fully deferred result,
`_convertForwardBudget` followed by `_settleMarketForwards`,
`_compoundLiquidity`, and `releaseClosedMarketCredit`.
-/

structure TokenAmounts where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq

structure FeeRouteCarry where
  toX : TokenAmounts
  toY : TokenAmounts
  lp : TokenAmounts
  deriving Repr, DecidableEq

structure RehypeAccounting where
  carry : FeeRouteCarry
  /-- Reservation contributed by the modeled market; equal to its carry. -/
  reservedX : Nat
  reservedY : Nat
  /-- Aggregate reservations of all other registered markets sharing X/Y. -/
  otherReservedX : Nat
  otherReservedY : Nat
  /-- DAMM credit owned by the fee manager in token X/Y at settled boundaries. -/
  managerCreditX : Nat
  managerCreditY : Nat
  /-- Ghost: fee credit currently denominated in X, including settled uses. -/
  originX : Nat
  /-- Ghost: fee credit currently denominated in Y, including settled uses. -/
  originY : Nat
  /-- Ghost: aggregate credit paid to beneficiaries by token denomination. -/
  paidX : Nat
  paidY : Nat
  /-- Ghost: aggregate credit consumed by successful full-range provides. -/
  compoundedX : Nat
  compoundedY : Nat
  deriving Repr, DecidableEq

def carryX (s : RehypeAccounting) : Nat :=
  s.carry.toX.x + s.carry.toY.x + s.carry.lp.x

def carryY (s : RehypeAccounting) : Nat :=
  s.carry.toX.y + s.carry.toY.y + s.carry.lp.y

def totalReservedX (s : RehypeAccounting) : Nat :=
  s.reservedX + s.otherReservedX

def totalReservedY (s : RehypeAccounting) : Nat :=
  s.reservedY + s.otherReservedY

/-- Source `_onSwapFeeReceived`, token-X branch after exact WAD routing. -/
def _onSwapFeeReceivedX
    (s : RehypeAccounting) (fee stay convert lp : Nat) : RehypeAccounting :=
  { s with
    carry := { s.carry with
      toX := { s.carry.toX with x := s.carry.toX.x + stay }
      toY := { s.carry.toY with x := s.carry.toY.x + convert }
      lp := { s.carry.lp with x := s.carry.lp.x + lp } }
    reservedX := s.reservedX + fee
    managerCreditX := s.managerCreditX + fee
    originX := s.originX + fee }

/-- Source `_onSwapFeeReceived`, token-Y branch after exact WAD routing. -/
def _onSwapFeeReceivedY
    (s : RehypeAccounting) (fee stay convert lp : Nat) : RehypeAccounting :=
  { s with
    carry := { s.carry with
      toY := { s.carry.toY with y := s.carry.toY.y + stay }
      toX := { s.carry.toX with y := s.carry.toX.y + convert }
      lp := { s.carry.lp with y := s.carry.lp.y + lp } }
    reservedY := s.reservedY + fee
    managerCreditY := s.managerCreditY + fee
    originY := s.originY + fee }

/-- `processFees` terminal branch when no external leg succeeds and every carry
cell is unchanged. A `false` result after a successful conversion or balancing
swap is represented by the corresponding non-identity transition below. -/
def processFeesDeferred (s : RehypeAccounting) : RehypeAccounting := s

/--
Successful X-to-Y `_convertForwardBudget` composed with the same-pass
`_settleMarketForwards`. Unspent input remains in `toY.x`; realized Y is paid
once and never enters next carry.
-/
def convertForwardXToYAndSettle
    (s : RehypeAccounting) (spent received : Nat) : RehypeAccounting :=
  { s with
    carry := { s.carry with
      toY := { s.carry.toY with x := s.carry.toY.x - spent } }
    reservedX := s.reservedX - spent
    managerCreditX := s.managerCreditX - spent
    originX := s.originX - spent
    originY := s.originY + received
    paidY := s.paidY + received }

/-- Y-to-X symmetric conversion and same-pass settlement. -/
def convertForwardYToXAndSettle
    (s : RehypeAccounting) (spent received : Nat) : RehypeAccounting :=
  { s with
    carry := { s.carry with
      toX := { s.carry.toX with y := s.carry.toX.y - spent } }
    reservedY := s.reservedY - spent
    managerCreditY := s.managerCreditY - spent
    originY := s.originY - spent
    originX := s.originX + received
    paidX := s.paidX + received }

/-- Settle already destination-denominated forward rows. -/
def _settleMarketForwards
    (s : RehypeAccounting) (forwardedX forwardedY : Nat) : RehypeAccounting :=
  { s with
    carry := { s.carry with
      toX := { s.carry.toX with x := s.carry.toX.x - forwardedX }
      toY := { s.carry.toY with y := s.carry.toY.y - forwardedY } }
    reservedX := s.reservedX - forwardedX
    reservedY := s.reservedY - forwardedY
    managerCreditX := s.managerCreditX - forwardedX
    managerCreditY := s.managerCreditY - forwardedY
    paidX := s.paidX + forwardedX
    paidY := s.paidY + forwardedY }

/--
Successful X-to-Y LP balancing swap followed by a successful/partial provide.
Unprovided post-swap budgets become the next `lp` carry exactly as in
`_compoundLiquidity`.
-/
def _compoundLiquiditySellX
    (s : RehypeAccounting) (spent received providedX providedY : Nat) : RehypeAccounting :=
  let postX := s.carry.lp.x - spent
  let postY := s.carry.lp.y + received
  { s with
    carry := { s.carry with lp := { x := postX - providedX, y := postY - providedY } }
    reservedX := s.reservedX - spent - providedX
    reservedY := s.reservedY + received - providedY
    managerCreditX := s.managerCreditX - spent - providedX
    managerCreditY := s.managerCreditY + received - providedY
    originX := s.originX - spent
    originY := s.originY + received
    compoundedX := s.compoundedX + providedX
    compoundedY := s.compoundedY + providedY }

/-- Y-to-X symmetric LP balancing and provide transition. -/
def _compoundLiquiditySellY
    (s : RehypeAccounting) (spent received providedX providedY : Nat) : RehypeAccounting :=
  let postX := s.carry.lp.x + received
  let postY := s.carry.lp.y - spent
  { s with
    carry := { s.carry with lp := { x := postX - providedX, y := postY - providedY } }
    reservedX := s.reservedX + received - providedX
    reservedY := s.reservedY - spent - providedY
    managerCreditX := s.managerCreditX + received - providedX
    managerCreditY := s.managerCreditY - spent - providedY
    originX := s.originX + received
    originY := s.originY - spent
    compoundedX := s.compoundedX + providedX
    compoundedY := s.compoundedY + providedY }

/-- Closed-market token-affinity release of the complete carry. -/
def releaseClosedMarketCredit (s : RehypeAccounting) : RehypeAccounting :=
  let x := carryX s
  let y := carryY s
  { s with
    carry := { toX := { x := 0, y := 0 }, toY := { x := 0, y := 0 }, lp := { x := 0, y := 0 } }
    reservedX := s.reservedX - x
    reservedY := s.reservedY - y
    managerCreditX := s.managerCreditX - x
    managerCreditY := s.managerCreditY - y
    paidX := s.paidX + x
    paidY := s.paidY + y }

end Benchmark.Cases.Doppler.MulticurveFeeConservation
