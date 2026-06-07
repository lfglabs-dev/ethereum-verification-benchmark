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

/-- **CRITICAL_PATH L1** — Strict monotonicity per `(sender, key)`: a
    successful nonce check strictly increases the stored sequence number.
    Replay-protection primitive — once `(sender, key, seq)` is accepted,
    it can never be accepted again. -/
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

/-! ## `ValidationData` packed-word decomposition (item E)

Real Solidity packs three fields into a 256-bit `validationData` word
returned by `IAccount.validateUserOp` and `IPaymaster.validatePaymasterUserOp`:

```
uint160 aggregator        -- low 160 bits
uint48  validUntil        -- next  48 bits
uint48  validAfter        -- high  48 bits
```

The `aggregator` low half encodes:

* `address(0)` (= `SIG_VALIDATION_SUCCESS`) when the account fully approves.
* `address(1)` (= `SIG_VALIDATION_FAILED`) when the signature is invalid.
* any other address = "trusted aggregator address" — the bundler must
  invoke `handleAggregatedOps` with that aggregator.

The time window `[validAfter, validUntil]` (inclusive) constrains when
the op may be executed. `validUntil == 0` means "no upper bound".
EntryPoint's `_getValidationData` checks both fields after the call.

This module decomposes the packed word and proves the "validated" iff
"aggregator OK AND time window holds" biconditional.
-/

def TWO_POW_160 : Nat := 1461501637330902918203684832716283019655932542976
def TWO_POW_48  : Nat := 281474976710656

/-- The low-160 aggregator field. -/
def vdAggregator (w : Uint256) : Nat := (w : Nat) % TWO_POW_160

/-- The middle-48 `validUntil` field. -/
def vdValidUntil (w : Uint256) : Nat := ((w : Nat) / TWO_POW_160) % TWO_POW_48

/-- The high-48 `validAfter` field. -/
def vdValidAfter (w : Uint256) : Nat :=
  ((w : Nat) / TWO_POW_160 / TWO_POW_48) % TWO_POW_48

/-- The two sentinel values from `_packValidationData(uint256(SIG_VALIDATION_*))`. -/
def SIG_VALIDATION_SUCCESS : Nat := 0
def SIG_VALIDATION_FAILED  : Nat := 1

/-- A `validationData` word reflects "success" iff its aggregator field is 0. -/
def vdAggregatorSuccess (w : Uint256) : Bool :=
  decide (vdAggregator w = SIG_VALIDATION_SUCCESS)

/-- A `validationData` word's time window covers `now` iff
    `validAfter ≤ now ∧ (validUntil = 0 ∨ now ≤ validUntil)`. -/
def vdTimeWindowOk (w : Uint256) (now : Nat) : Bool :=
  decide (vdValidAfter w ≤ now ∧ (vdValidUntil w = 0 ∨ now ≤ vdValidUntil w))

/-- The full "validated" predicate: aggregator success AND time window. -/
def vdValid (w : Uint256) (now : Nat) : Bool :=
  vdAggregatorSuccess w && vdTimeWindowOk w now

/-! ### Lemmas about the packed-word decomposition -/

/-- A pure-success word (aggregator = 0, no time bounds) yields validation. -/
theorem vdValid_of_success_word (now : Nat) :
    vdValid 0 now = true := by
  unfold vdValid vdAggregatorSuccess vdTimeWindowOk
  unfold vdAggregator vdValidUntil vdValidAfter
  simp [SIG_VALIDATION_SUCCESS]

/-- An aggregator-failure word never validates. -/
theorem vdValid_false_if_aggregator_nonzero (w : Uint256) (now : Nat)
    (h : vdAggregator w ≠ SIG_VALIDATION_SUCCESS) :
    vdValid w now = false := by
  unfold vdValid vdAggregatorSuccess
  simp [h]

/-- A `now` outside the window invalidates the word. -/
theorem vdValid_false_if_time_after_until (w : Uint256) (now : Nat)
    (hUntil : vdValidUntil w ≠ 0) (hOOB : vdValidUntil w < now) :
    vdValid w now = false := by
  unfold vdValid vdTimeWindowOk
  apply Bool.and_eq_false_iff.mpr
  right
  apply decide_eq_false
  rintro ⟨_, hcase⟩
  rcases hcase with hu | hn
  · exact hUntil hu
  · omega

theorem vdValid_false_if_time_before_after (w : Uint256) (now : Nat)
    (hOOB : now < vdValidAfter w) :
    vdValid w now = false := by
  unfold vdValid vdTimeWindowOk
  apply Bool.and_eq_false_iff.mpr
  right
  apply decide_eq_false
  rintro ⟨h, _⟩
  omega

end Benchmark.Cases.ERC4337.EntryPointInvariant
