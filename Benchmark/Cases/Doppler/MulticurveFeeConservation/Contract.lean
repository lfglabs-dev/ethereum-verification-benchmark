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
* `tokenX` and `tokenY` are represented as distinct token denominations.
  Same-address token-pair aliasing is outside this accounting projection.
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

/-- One independently succeeding or deferred forward-conversion leg. -/
inductive ForwardLegOutcome where
  | deferred
  | converted (spent received : Nat)
  deriving Repr, DecidableEq

/-- The LP leg either fully defers or records one balancing direction and the
exact successful swap/provide results. `liquidityAdded` is used only for the
source-compatible `processFees` Boolean result. -/
inductive LpLegOutcome where
  | deferred
  | sellX (spent received providedX providedY liquidityAdded : Nat)
  | sellY (spent received providedX providedY liquidityAdded : Nat)
  deriving Repr, DecidableEq

/-- Finite process plan for both forward legs, the optional LP branch, and the
aggregate nested callbacks that must merge into next carry. -/
structure ProcessFeesPlan where
  callbackFeeX : Nat
  callbackStayX : Nat
  callbackConvertX : Nat
  callbackLpX : Nat
  callbackFeeY : Nat
  callbackStayY : Nat
  callbackConvertY : Nat
  callbackLpY : Nat
  forwardToX : ForwardLegOutcome
  forwardToY : ForwardLegOutcome
  lp : LpLegOutcome
  deriving Repr, DecidableEq

def applyForwardToX (s : RehypeAccounting) : ForwardLegOutcome → RehypeAccounting
  | .deferred => s
  | .converted spent received => convertForwardYToXAndSettle s spent received

def applyForwardToY (s : RehypeAccounting) : ForwardLegOutcome → RehypeAccounting
  | .deferred => s
  | .converted spent received => convertForwardXToYAndSettle s spent received

def applyLpLeg (s : RehypeAccounting) : LpLegOutcome → RehypeAccounting
  | .deferred => s
  | .sellX spent received providedX providedY _ =>
      _compoundLiquiditySellX s spent received providedX providedY
  | .sellY spent received providedX providedY _ =>
      _compoundLiquiditySellY s spent received providedX providedY

def forwardReceived : ForwardLegOutcome → Nat
  | .deferred => 0
  | .converted _ received => received

def lpLiquidityAdded : LpLegOutcome → Nat
  | .deferred => 0
  | .sellX _ _ _ _ liquidityAdded => liquidityAdded
  | .sellY _ _ _ _ liquidityAdded => liquidityAdded

/-- Source-compatible `processFees` return value. Successful swaps may occur
while this is false when neither forwarding nor liquidity provision succeeds. -/
def processFeesProcessed (s : RehypeAccounting) (p : ProcessFeesPlan) : Bool :=
  decide (s.carry.toX.x + forwardReceived p.forwardToX != 0 ∨
    s.carry.toY.y + forwardReceived p.forwardToY != 0 ∨
    lpLiquidityAdded p.lp != 0)

/--
Settled-boundary effect of one complete `processFees` invocation. Same-token
snapshot settlement is normalized first, followed by the two independent
forward-conversion outcomes and the optional LP outcome. Aggregate nested
callback additions are normalized to the end because the source writes them to
next carry and old-snapshot processing may not consume them. This retains every
independent success/defer combination, including `false` after a successful
conversion or balancing swap.
-/
def processFeesStep (s : RehypeAccounting) (p : ProcessFeesPlan) : Bool × RehypeAccounting :=
  let s0 := _settleMarketForwards s s.carry.toX.x s.carry.toY.y
  let s1 := applyForwardToX s0 p.forwardToX
  let s2 := applyForwardToY s1 p.forwardToY
  let s3 := applyLpLeg s2 p.lp
  let s4 := _onSwapFeeReceivedX s3 p.callbackFeeX p.callbackStayX p.callbackConvertX p.callbackLpX
  let s5 := _onSwapFeeReceivedY s4 p.callbackFeeY p.callbackStayY p.callbackConvertY p.callbackLpY
  (processFeesProcessed s p, s5)

end Benchmark.Cases.Doppler.MulticurveFeeConservation
