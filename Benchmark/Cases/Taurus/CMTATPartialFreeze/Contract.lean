import Verity.Core.Address
import Verity.Core.Uint256

/-!
CMTAT v3.0.0, 69eecc9735ce8ada84fd35801888b05747658939.
Source-shaped semantic model using Verity's bounded Address/Uint256 types,
not a verity_contract DSL compilation or a bytecode refinement.

Scope: standard CMTAT transfer/transferFrom with RuleEngine and SnapshotEngine
unset at EVERY operation. Their configured callback branches, custom subclasses,
ERC1363 receiver callbacks, proxy upgrades and privileged money movement are not
modeled. The model does not assert that arbitrary configured engines are safe.

Storage namespaces become named functional fields, not literal ERC7201 slots.
Resolved caller is explicit; ERC2771 forwarder authentication is not proved.
Events, bytes data, metadata and document/debt operations are omitted. The
ordinary trace alphabet contains no administrative writers or approve. Partial
freeze writers are separate helpers retaining effective ERC20ENFORCER_ROLE
(including the source's effective default-admin satisfaction).

Checked subtraction reverts before Nat subtraction; unchecked recipient addition
wraps modulo 2^256 with no extra overflow guard. Sender debit occurs BEFORE the
recipient read, preserving self-transfer aliasing. No total-supply/recipient
backing theorem is asserted for arbitrary synthetic states. Source/model match
is hand reviewed; original source and imported dependency are pinned in run notes.
-/
namespace Benchmark.Cases.Taurus.CMTATPartialFreeze
open Verity.Core

abbrev Word := Uint256
abbrev Account := Address
def modulus : Nat := Uint256.modulus
def maxWord : Word := Uint256.ofNat (modulus - 1)
def word (n : Nat) : Word := Uint256.ofNat n

structure State where
  balances : Account → Word
  frozenTokens : Account → Word
  allowances : Account → Account → Word
  addressFrozen : Account → Bool
  paused : Bool
  deactivated : Bool
  erc20Enforcer : Account → Bool
  defaultAdmin : Account → Bool

inductive Error where
  | arithmeticUnderflow | arithmeticOverflow | activeBalance | invalidTransfer
  | invalidSender | invalidReceiver | invalidApprover | invalidSpender
  | insufficientBalance | insufficientAllowance | exceedsBalance
  | exceedsFrozen | unauthorized
  deriving DecidableEq, Repr

abbrev Result := Except Error State

def balanceOf (s : State) (a : Account) : Nat := (s.balances a).val
def getFrozenTokens (s : State) (a : Account) : Nat := (s.frozenTokens a).val

def _checkActiveBalance (s : State) (src : Account) (value : Word) : Except Error Bool :=
  let frozen := getFrozenTokens s src
  if frozen > 0 then
    if balanceOf s src < frozen then .error .arithmeticUnderflow
    else .ok (decide (value.val ≤ balanceOf s src - frozen))
  else .ok true

def _canMintBurnByModule (s : State) (target : Account) : Bool :=
  !(s.deactivated || s.addressFrozen target)

def _canTransferGenericByModule (s : State) (spender src to : Account) : Bool :=
  if src = 0 then _canMintBurnByModule s to
  else if to = 0 then _canMintBurnByModule s src
  else !(s.addressFrozen spender || s.addressFrozen src || s.addressFrozen to || s.paused)

def _checkTransferred (s : State) (spender src to : Account) (value : Word) : Except Error Unit := do
  let active ← _checkActiveBalance s src value
  if !active then throw .activeBalance
  if !(_canTransferGenericByModule s spender src to) then throw .invalidTransfer
  pure ()

def _update (s : State) (src to : Account) (value : Word) : Result :=
  if balanceOf s src < value.val then .error .insufficientBalance
  else
    let debited := { s with balances := fun a => if a = src then word (balanceOf s src - value.val) else s.balances a }
    .ok { debited with balances := fun a => if a = to then word (balanceOf debited to + value.val) else debited.balances a }

def _transfer (s : State) (src to : Account) (value : Word) : Result :=
  if src = 0 then .error .invalidSender
  else if to = 0 then .error .invalidReceiver
  else _update s src to value

def _approve (s : State) (owner spender : Account) (value : Word) : Result :=
  if owner = 0 then .error .invalidApprover
  else if spender = 0 then .error .invalidSpender
  else .ok { s with allowances := fun a b => if a = owner ∧ b = spender then value else s.allowances a b }

def _spendAllowance (s : State) (owner spender : Account) (value : Word) : Result :=
  let current := (s.allowances owner spender).val
  if current = modulus - 1 then .ok s
  else if current < value.val then .error .insufficientAllowance
  else _approve s owner spender (word (current - value.val))

def transfer (s : State) (caller to : Account) (value : Word) : Result := do
  _checkTransferred s 0 caller to value
  _transfer s caller to value

def transferFrom (s : State) (caller src to : Account) (value : Word) : Result := do
  _checkTransferred s caller src to value
  let approved ← _spendAllowance s src caller value
  _transfer approved src to value

def freezePartialTokens (s : State) (caller account : Account) (value : Word) : Result :=
  if !(s.erc20Enforcer caller || s.defaultAdmin caller) then .error .unauthorized
  else
    let next := getFrozenTokens s account + value.val
    if next ≥ modulus then .error .arithmeticOverflow
    else if balanceOf s account < next then .error .exceedsBalance
    else .ok { s with frozenTokens := fun a => if a = account then word next else s.frozenTokens a }

def unfreezePartialTokens (s : State) (caller account : Account) (value : Word) : Result :=
  if !(s.erc20Enforcer caller || s.defaultAdmin caller) then .error .unauthorized
  else if getFrozenTokens s account < value.val then .error .exceedsFrozen
  else .ok { s with frozenTokens := fun a => if a = account then word (getFrozenTokens s account - value.val) else s.frozenTokens a }

inductive Operation where
  | transfer (caller to : Account) (value : Word)
  | transferFrom (caller src to : Account) (value : Word)

def Operation.sender : Operation → Account
  | .transfer caller _ _ => caller
  | .transferFrom _ src _ _ => src

def Operation.recipient : Operation → Account
  | .transfer _ to _ => to
  | .transferFrom _ _ to _ => to

def Operation.amount : Operation → Word
  | .transfer _ _ value => value
  | .transferFrom _ _ _ value => value

def run (s : State) : Operation → Result
  | .transfer caller to value => transfer s caller to value
  | .transferFrom caller src to value => transferFrom s caller src to value

/-- EVM atomicity wrapper: any error returns the entire original state. -/
def transact (s : State) (op : Operation) : Bool × State :=
  match run s op with
  | .error _ => (false, s)
  | .ok next => (true, next)

end Benchmark.Cases.Taurus.CMTATPartialFreeze
