import Contracts.Common

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# `PackedUserOperation` + 2D nonce

Faithful Lean models of the two real Solidity types the headline
biconditional must mention by name:

* `PackedUserOperation`: the user-supplied input to `handleOps`, packed
  the way the source file packs it (sender, nonce, initCode, callData,
  accountGasLimits, preVerificationGas, gasFees, paymasterAndData,
  signature).

* `Nonce2D`: the `nonce` field decomposes as `uint192 key` (high 192
  bits) and `uint64 sequenceNumber` (low 64). `NonceManager` stores
  `mapping(address => mapping(uint192 => uint256))`. The post-increment
  `nonceSequenceNumber[sender][key]++` is the replay-protection
  primitive.

These types let us state Yoav's theorem in its real form
(`countExecCalls trace ops[i].sender ops[i].callData = ...`) rather than
the abstracted `key : Uint256` shape used in `EntryPointV09.lean`.
-/

/-- The packed user operation. Bytes-shaped fields are represented as
    `List Uint256` (word-list) for the purpose of stating the invariant;
    the actual ABI encoding lives in the Verity compiler and is
    orthogonal to the proof. -/
structure PackedUserOperation where
  sender              : Address
  nonce               : Uint256
  initCode            : List Uint256
  callData            : List Uint256
  accountGasLimits    : Uint256   -- packed: callGasLimit << 128 | verificationGasLimit
  preVerificationGas  : Uint256
  gasFees             : Uint256   -- packed: maxFeePerGas << 128 | maxPriorityFeePerGas
  paymasterAndData    : List Uint256 -- empty list = no paymaster
  signature           : List Uint256
  deriving Repr

/-- `true` iff the op declares a paymaster (`paymasterAndData` non-empty
    and its first 20 bytes encode a non-zero address). We collapse the
    address-check to "non-empty list" because the paymaster address
    decoding sits at the ABI layer and the invariant only cares about
    the *presence* of a paymaster. -/
def hasPaymaster (op : PackedUserOperation) : Bool :=
  ¬ op.paymasterAndData.isEmpty

/-- `true` iff the op declares an `initCode` deployment. -/
def hasInitCode (op : PackedUserOperation) : Bool :=
  ¬ op.initCode.isEmpty

/-- `true` iff the op has a non-empty `callData`. This is the predicate
    that gates the `Exec.call(sender, ..., callData)` branch inside
    `innerHandleOp`. -/
def hasCallData (op : PackedUserOperation) : Bool :=
  ¬ op.callData.isEmpty

/-! ## Nonce decomposition

The Solidity source:
```
function _validateAndUpdateNonce(address sender, uint256 nonce) {
  uint192 key = uint192(nonce >> 64);
  uint64 seq = uint64(nonce);
  require(nonceSequenceNumber[sender][key]++ == seq);
}
```

We model `uint192` and `uint64` as `Nat` bounded by their respective
maxima. The decomposition is total: every `Uint256` corresponds to a
unique (key, seq) pair.
-/

/-- `2^64` — the modulus for the low half of a packed nonce. -/
def TWO_POW_64 : Nat := 18446744073709551616

/-- Maximum value of a `uint192`. -/
def MAX_UINT192 : Nat := 6277101735386680763835789423207666416102355444464034512895

/-- The `uint192` key extracted from a packed nonce: `nonce >> 64`. -/
def nonceKey (n : Uint256) : Nat := (n : Nat) / TWO_POW_64

/-- The `uint64` sequence number from a packed nonce: low 64 bits. -/
def nonceSeq (n : Uint256) : Nat := (n : Nat) % TWO_POW_64

/-- Reconstruction: `nonce = key << 64 | seq`. -/
def nonceCompose (key seq : Nat) : Nat := key * TWO_POW_64 + seq

/-- Decomposition is a left-inverse of composition. -/
theorem nonceSeq_compose (key seq : Nat) (hSeq : seq < TWO_POW_64) :
    nonceCompose key seq % TWO_POW_64 = seq := by
  unfold nonceCompose
  have : (key * TWO_POW_64 + seq) % TWO_POW_64 = seq % TWO_POW_64 := by
    conv_lhs => rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  rw [this, Nat.mod_eq_of_lt hSeq]

theorem nonceKey_compose (key seq : Nat) (hSeq : seq < TWO_POW_64) :
    nonceCompose key seq / TWO_POW_64 = key := by
  unfold nonceCompose
  have hPos : 0 < TWO_POW_64 := by decide
  have h1 : (key * TWO_POW_64 + seq) / TWO_POW_64 =
            (TWO_POW_64 * key + seq) / TWO_POW_64 := by rw [Nat.mul_comm]
  rw [h1, Nat.mul_add_div hPos, Nat.div_eq_of_lt hSeq, Nat.add_zero]

/-- 2D nonce table: `address sender → uint192 key → uint64 sequenceNumber`. -/
abbrev Nonce2DTable := Address → Nat → Nat

/-- Read the current sequence number for `(sender, key)`. -/
def readNonceSeq (table : Nonce2DTable) (sender : Address) (key : Nat) : Nat :=
  table sender key

/-- Increment the sequence number at `(sender, key)`. -/
def bumpNonceSeq (table : Nonce2DTable) (sender : Address) (key : Nat)
    : Nonce2DTable :=
  fun s k => if s = sender ∧ k = key then table sender key + 1 else table s k

/-- The validation predicate `NonceManager._validateAndUpdateNonce` checks:
    the stored `nonceSequenceNumber[sender][key]` equals `uint64(nonce)`. -/
def nonceMatches (table : Nonce2DTable) (sender : Address) (n : Uint256) : Bool :=
  decide (readNonceSeq table sender (nonceKey n) = nonceSeq n)

/-! ## Replay-protection lemmas (critical-path) -/

/-- **Strict monotonicity per `(sender, key)`**: a successful nonce check
    strictly increases the stored sequence number. This is the
    replay-protection primitive — once `(sender, key, seq)` has been
    accepted, it can never be accepted again. -/
theorem bump_strictly_increases
    (table : Nonce2DTable) (sender : Address) (key : Nat) :
    readNonceSeq (bumpNonceSeq table sender key) sender key =
    readNonceSeq table sender key + 1 := by
  unfold readNonceSeq bumpNonceSeq
  simp

/-- **Replay rejection**: after bumping, the same `(sender, n)` pair no
    longer satisfies `nonceMatches` (provided the original match held). -/
theorem replay_rejected
    (table : Nonce2DTable) (sender : Address) (n : Uint256)
    (hMatch : nonceMatches table sender n = true) :
    nonceMatches (bumpNonceSeq table sender (nonceKey n)) sender n = false := by
  unfold nonceMatches at hMatch ⊢
  simp at hMatch
  rw [bump_strictly_increases]
  simp
  omega

/-- **Disjoint-key independence**: bumping `(sender, k₁)` does not affect
    `(sender', k₂)` when `(sender', k₂) ≠ (sender, k₁)`. -/
theorem bump_preserves_other_keys
    (table : Nonce2DTable) (sender sender' : Address) (k k' : Nat)
    (h : ¬ (sender' = sender ∧ k' = k)) :
    readNonceSeq (bumpNonceSeq table sender k) sender' k' =
    readNonceSeq table sender' k' := by
  unfold readNonceSeq bumpNonceSeq
  simp [h]

end Benchmark.Cases.ERC4337.EntryPointInvariant
