import Mathlib.Data.List.Basic

namespace Benchmark.Cases.Zodiac.RolesDecoderFaithfulness

/-
  Focused model of the Zodiac Roles v3 lazy ABI decoder.

  Upstream:
  - Repository: https://github.com/gnosisguild/zodiac-modifier-roles
  - Branch: contracts-v3
  - Commit: 172723b165d482c5565e413e9927604b0dc168b6
  - Files:
    packages/evm/contracts/common/AbiLocation.sol
    packages/evm/contracts/core/serialize/Topology.sol
    packages/evm/contracts/core/evaluate/ConditionEvaluator.sol
    packages/evm/contracts/core/serialize/Integrity.sol
    packages/evm/contracts/types/Condition.sol

  Simplifications and boundaries:
  - The packed `ConditionFlat[]` representation is modeled as a finite ABI type
    tree (`AbiTy`). The Integrity + pack/unpack bridge is assumed only at the
    manifest level: well-formed metadata uses `rolesIsInlined` and
    `rolesInlinedSize` below.
  - Calldata is a byte length plus a guarded 32-byte word reader. The contract
    guards reads before `calldataload`, so overflow is modeled as an explicit
    sentinel rather than EVM zero-fill.
  - Byte equality is represented by equality of `(start, size)` regions.
  - `staticWords n` stands for one or more canonical ABI static words. This is
    intentionally a word-granular model, not a bit-level model of every Solidity
    static base type.
  - `transparent child` models the `Encoding.None` wrapper used by logical
    conditions. Other `None` variants and `Encoding.EtherValue` are out of
    scope.
  - Recursive walkers are fuel-bounded. `decoderValueFuel = 256` bounds encoded
    size computation, and top-level leaf navigation uses `path.length + 64`.
    Exhausting fuel returns `DecodeResult.overflow`; this is conservative for
    bounds safety but makes extremely deep wrapper trees vacuous in this model.
  - The reference is a hand-written canonical-layout model. It is independent of
    Roles' packed metadata and helper names, but it is still an in-repository
    transcription of ABI v2 layout rather than an external oracle.
  - Out of scope: `Operator.Custom`, `Zip`, `Slice`, `Pluck`,
    `MultiSendUnwrapper`, condition-consumption state, comparison operators,
    and external calls.

  The reference decoder in this file is deliberately not implemented through
  Roles' `AbiLocation.children`, `AbiLocation.size`, or Topology metadata. It is
  a hand-written canonical Solidity ABI v2 layout model: static values are in the HEAD,
  dynamic entries are 32-byte HEAD offsets relative to the ABI block start,
  bytes/string/AbiEncoded payloads start with a length word, dynamic-array
  element blocks start after the array length word, and dynamic payload sizes
  are rounded with `ceil32`.
-/

inductive AbiTy where
  | staticWords : Nat -> AbiTy
  | dynamicBytes : AbiTy
  | string : AbiTy
  | tuple : List AbiTy -> AbiTy
  | dynamicArray : AbiTy -> AbiTy
  | abiEncoded : AbiTy -> AbiTy
  | transparent : AbiTy -> AbiTy
  deriving Repr, BEq, Inhabited

structure Calldata where
  len : Nat
  wordAt : Nat -> Nat

structure Region where
  start : Nat
  size : Nat
  deriving Repr, BEq, Inhabited

inductive DecodeResult where
  | ok : Region -> DecodeResult
  | overflow : DecodeResult
  deriving Repr, BEq, Inhabited

def wordSize : Nat := 32
def selectorSize : Nat := 4

def ceil32 (n : Nat) : Nat :=
  ((n + 31) / 32) * 32

def guardedWord (data : Calldata) (pos : Nat) : Option Nat :=
  if pos + wordSize <= data.len then some (data.wordAt pos) else none

def inBounds (data : Calldata) (r : Region) : Bool :=
  r.start + r.size <= data.len

def nonForwardTail (headOffset tailOffset : Nat) : Bool :=
  tailOffset <= headOffset

def dynamicPayloadRegion (data : Calldata) (location : Nat) : DecodeResult :=
  match guardedWord data location with
  | none => .overflow
  | some n =>
      let r := { start := location, size := wordSize + ceil32 n }
      if inBounds data r then .ok r else .overflow

def safeTailFromHead
    (data : Calldata) (blockStart headOffset : Nat) : Option Nat :=
  if blockStart + headOffset + wordSize > data.len then
    none
  else
    let tailOffset := data.wordAt (blockStart + headOffset)
    if nonForwardTail headOffset tailOffset then
      none
    else if blockStart + tailOffset + wordSize > data.len then
      none
    else
      some (blockStart + tailOffset)

def canonicalTailStart
    (data : Calldata) (blockStart headOffset : Nat) : Option Nat :=
  match guardedWord data (blockStart + headOffset) with
  | none => none
  | some tailOffset =>
      if tailOffset <= headOffset then
        none
      else if blockStart + tailOffset + wordSize <= data.len then
        some (blockStart + tailOffset)
      else
        none

def sumMapTake (f : α -> Nat) : List α -> Nat -> Nat
  | [], _ => 0
  | _, 0 => 0
  | x :: xs, n + 1 => f x + sumMapTake f xs n

def childAt? (xs : List AbiTy) (i : Nat) : Option AbiTy :=
  xs[i]?

mutual
  /-- Independent canonical ABI staticness predicate. -/
  def abiStatic : AbiTy -> Bool
    | .staticWords _ => true
    | .tuple xs => abiStaticList xs
    | .transparent child => abiStatic child
    | .dynamicBytes => false
    | .string => false
    | .dynamicArray _ => false
    | .abiEncoded _ => false

  def abiStaticList : List AbiTy -> Bool
    | [] => true
    | x :: xs => abiStatic x && abiStaticList xs
end

mutual
  /-- Independent canonical ABI byte width for values that are static in-place.
      Dynamic values have metadata size zero; their HEAD entry width is the
      ABI offset word supplied by `abiHeadEntryWidth`. -/
  def abiStaticBytes : AbiTy -> Nat
    | .staticWords n => n * wordSize
    | .tuple xs => abiStaticBytesList xs
    | .transparent child => abiStaticBytes child
    | .dynamicBytes => 0
    | .string => 0
    | .dynamicArray _ => 0
    | .abiEncoded _ => 0

  def abiStaticBytesList : List AbiTy -> Nat
    | [] => 0
    | x :: xs => abiStaticBytes x + abiStaticBytesList xs
end

def abiHeadEntryWidth (t : AbiTy) : Nat :=
  if abiStatic t then abiStaticBytes t else wordSize

def abiHeadOffsetBefore (children : List AbiTy) (i : Nat) : Nat :=
  sumMapTake abiHeadEntryWidth children i

mutual
  /-- Model of `Topology.isInlined`, separated from `abiStatic`. -/
  def rolesIsInlined : AbiTy -> Bool
    | .staticWords _ => true
    | .tuple xs => rolesIsInlinedList xs
    | .transparent child => rolesIsInlined child
    | .dynamicBytes => false
    | .string => false
    | .dynamicArray _ => false
    | .abiEncoded _ => false

  def rolesIsInlinedList : List AbiTy -> Bool
    | [] => true
    | x :: xs => rolesIsInlined x && rolesIsInlinedList xs
end

mutual
  /-- Model of `Topology.inlinedSize`, separated from `abiStaticBytes`. -/
  def rolesInlinedSize : AbiTy -> Nat
    | .staticWords n => n * wordSize
    | .tuple xs => rolesInlinedSizeList xs
    | .transparent child => rolesInlinedSize child
    | .dynamicBytes => 0
    | .string => 0
    | .dynamicArray _ => 0
    | .abiEncoded _ => 0

  def rolesInlinedSizeList : List AbiTy -> Nat
    | [] => 0
    | x :: xs => rolesInlinedSize x + rolesInlinedSizeList xs
end

def rolesHeadEntryWidth (t : AbiTy) : Nat :=
  if rolesIsInlined t then rolesInlinedSize t else wordSize

def rolesHeadOffsetBefore (children : List AbiTy) (i : Nat) : Nat :=
  sumMapTake rolesHeadEntryWidth children i

def decoderValueFuel (_t : AbiTy) : Nat :=
  256

def rolesChildBlock
    (data : Calldata) (blockStart : Nat) (children : List AbiTy) (i : Nat) :
    Option (AbiTy × Nat) :=
  match childAt? children i with
  | none => none
  | some child =>
      let headOffset := rolesHeadOffsetBefore children i
      if rolesIsInlined child then
        let childLocation := blockStart + headOffset
        if childLocation <= data.len then some (child, childLocation) else none
      else
        match safeTailFromHead data blockStart headOffset with
        | none => none
        | some childLocation => some (child, childLocation)

def rolesDynamicElementBlock
    (data : Calldata) (elementsBlockStart : Nat) (i : Nat) : Option Nat :=
  safeTailFromHead data elementsBlockStart (i * wordSize)

def refTupleChildBlock
    (data : Calldata) (blockStart : Nat) (children : List AbiTy) (i : Nat) :
    Option (AbiTy × Nat) :=
  match childAt? children i with
  | none => none
  | some child =>
      let headOffset := abiHeadOffsetBefore children i
      if abiStatic child then
        let childLocation := blockStart + headOffset
        if childLocation <= data.len then some (child, childLocation) else none
      else
        match canonicalTailStart data blockStart headOffset with
        | none => none
        | some childLocation => some (child, childLocation)

def refDynamicElementBlock
    (data : Calldata) (elementsBlockStart : Nat) (i : Nat) : Option Nat :=
  canonicalTailStart data elementsBlockStart (i * wordSize)

def addSizes (a b : DecodeResult) : DecodeResult :=
  match a, b with
  | .ok ra, .ok rb => .ok { start := ra.start, size := ra.size + rb.size }
  | _, _ => .overflow

mutual
def rolesTupleTailSizesFuel
    (fuel : Nat) (data : Calldata) (blockStart headCursor : Nat)
    (children : List AbiTy) : DecodeResult :=
  match fuel, children with
  | 0, _ => .overflow
  | _, [] => .ok { start := blockStart, size := 0 }
  | fuel' + 1, child :: rest =>
      let entryWidth := rolesHeadEntryWidth child
      let restSize := rolesTupleTailSizesFuel fuel' data blockStart
        (headCursor + entryWidth) rest
      if rolesIsInlined child then
        addSizes (.ok { start := blockStart, size := entryWidth }) restSize
      else
        match safeTailFromHead data blockStart headCursor with
        | none => .overflow
        | some childLocation =>
            addSizes (.ok { start := blockStart, size := wordSize })
              (addSizes (rolesEncodedSizeFuel fuel' data childLocation child) restSize)

termination_by fuel

def rolesArrayElementSizesFuel
    (fuel : Nat) (data : Calldata) (elementsBlockStart : Nat)
    (elem : AbiTy) (i count : Nat) : DecodeResult :=
  match fuel with
  | 0 => .overflow
  | fuel' + 1 =>
      if i < count then
        let restSize := rolesArrayElementSizesFuel fuel' data elementsBlockStart elem (i + 1) count
        if rolesIsInlined elem then
          addSizes (.ok { start := elementsBlockStart, size := rolesInlinedSize elem }) restSize
        else
          match rolesDynamicElementBlock data elementsBlockStart i with
          | none => .overflow
          | some elemLocation =>
              addSizes (.ok { start := elementsBlockStart, size := wordSize })
                (addSizes (rolesEncodedSizeFuel fuel' data elemLocation elem) restSize)
      else
        .ok { start := elementsBlockStart, size := 0 }

termination_by fuel

def rolesEncodedSizeFuel
    (fuel : Nat) (data : Calldata) (location : Nat) (t : AbiTy) : DecodeResult :=
  match fuel with
  | 0 => .overflow
  | fuel' + 1 =>
      match t with
      | .staticWords n => .ok { start := location, size := n * wordSize }
      | .dynamicBytes => dynamicPayloadRegion data location
      | .string => dynamicPayloadRegion data location
      | .tuple children =>
          rolesTupleTailSizesFuel fuel' data location 0 children
      | .dynamicArray elem =>
          match guardedWord data location with
          | none => .overflow
          | some count =>
              addSizes (.ok { start := location, size := wordSize })
                (rolesArrayElementSizesFuel fuel' data (location + wordSize) elem 0 count)
      | .abiEncoded _ => dynamicPayloadRegion data location
      | .transparent child => rolesEncodedSizeFuel fuel' data location child

termination_by fuel
end

mutual
def refTupleTailSizesFuel
    (fuel : Nat) (data : Calldata) (blockStart headCursor : Nat)
    (children : List AbiTy) : DecodeResult :=
  match fuel, children with
  | 0, _ => .overflow
  | _, [] => .ok { start := blockStart, size := 0 }
  | fuel' + 1, child :: rest =>
      let entryWidth := abiHeadEntryWidth child
      let restSize := refTupleTailSizesFuel fuel' data blockStart
        (headCursor + entryWidth) rest
      if abiStatic child then
        addSizes (.ok { start := blockStart, size := entryWidth }) restSize
      else
        match canonicalTailStart data blockStart headCursor with
        | none => .overflow
        | some childLocation =>
            addSizes (.ok { start := blockStart, size := wordSize })
              (addSizes (refEncodedSizeFuel fuel' data childLocation child) restSize)

termination_by fuel

def refArrayElementSizesFuel
    (fuel : Nat) (data : Calldata) (elementsBlockStart : Nat)
    (elem : AbiTy) (i count : Nat) : DecodeResult :=
  match fuel with
  | 0 => .overflow
  | fuel' + 1 =>
      if i < count then
        let restSize := refArrayElementSizesFuel fuel' data elementsBlockStart elem (i + 1) count
        if abiStatic elem then
          addSizes (.ok { start := elementsBlockStart, size := abiStaticBytes elem }) restSize
        else
          match refDynamicElementBlock data elementsBlockStart i with
          | none => .overflow
          | some elemLocation =>
              addSizes (.ok { start := elementsBlockStart, size := wordSize })
                (addSizes (refEncodedSizeFuel fuel' data elemLocation elem) restSize)
      else
        .ok { start := elementsBlockStart, size := 0 }

termination_by fuel

def refEncodedSizeFuel
    (fuel : Nat) (data : Calldata) (location : Nat) (t : AbiTy) : DecodeResult :=
  match fuel with
  | 0 => .overflow
  | fuel' + 1 =>
      match t with
      | .staticWords n => .ok { start := location, size := n * wordSize }
      | .dynamicBytes => dynamicPayloadRegion data location
      | .string => dynamicPayloadRegion data location
      | .tuple children =>
          refTupleTailSizesFuel fuel' data location 0 children
      | .dynamicArray elem =>
          match guardedWord data location with
          | none => .overflow
          | some count =>
              addSizes (.ok { start := location, size := wordSize })
                (refArrayElementSizesFuel fuel' data (location + wordSize) elem 0 count)
      | .abiEncoded _ => dynamicPayloadRegion data location
      | .transparent child => refEncodedSizeFuel fuel' data location child

termination_by fuel
end

def rolesValueRegion (data : Calldata) (location : Nat) : AbiTy -> DecodeResult
  | t =>
      match rolesEncodedSizeFuel (decoderValueFuel t) data location t with
      | .overflow => .overflow
      | .ok r =>
          let out := { start := location, size := r.size }
          if inBounds data out then .ok out else .overflow

def refValueRegion (data : Calldata) (location : Nat) : AbiTy -> DecodeResult
  | t =>
      match refEncodedSizeFuel (decoderValueFuel t) data location t with
      | .overflow => .overflow
      | .ok r =>
          let out := { start := location, size := r.size }
          if inBounds data out then .ok out else .overflow

def rolesLeafRegionFuel
    (fuel : Nat) (data : Calldata) (location : Nat) (t : AbiTy)
    (path : List Nat) : DecodeResult :=
  match fuel with
  | 0 => .overflow
  | fuel' + 1 =>
      match path with
      | [] => rolesValueRegion data location t
      | i :: rest =>
          match t with
          | .tuple children =>
              match rolesChildBlock data location children i with
              | none => .overflow
              | some (child, childLocation) =>
                  rolesLeafRegionFuel fuel' data childLocation child rest
          | .dynamicArray elem =>
              match guardedWord data location with
              | none => .overflow
              | some count =>
                  if i < count then
                    let blockStart := location + wordSize
                    if rolesIsInlined elem then
                      rolesLeafRegionFuel fuel' data
                        (blockStart + i * rolesInlinedSize elem) elem rest
                    else
                      match safeTailFromHead data blockStart (i * wordSize) with
                      | none => .overflow
                      | some childLocation =>
                          rolesLeafRegionFuel fuel' data childLocation elem rest
                  else
                    .overflow
          | .abiEncoded inner =>
              match guardedWord data location with
              | none => .overflow
              | some _ => rolesLeafRegionFuel fuel' data (location + wordSize) inner path
          | .transparent child => rolesLeafRegionFuel fuel' data location child path
          | _ => .overflow

def refLeafRegionFuel
    (fuel : Nat) (data : Calldata) (blockStart : Nat) (t : AbiTy)
    (path : List Nat) : DecodeResult :=
  match fuel with
  | 0 => .overflow
  | fuel' + 1 =>
      match path with
      | [] => refValueRegion data blockStart t
      | i :: rest =>
          match t with
          | .tuple children =>
              match refTupleChildBlock data blockStart children i with
              | none => .overflow
              | some (child, childBlockStart) =>
                  refLeafRegionFuel fuel' data childBlockStart child rest
          | .dynamicArray elem =>
              match guardedWord data blockStart with
              | none => .overflow
              | some count =>
                  if i < count then
                    let elementsBlockStart := blockStart + wordSize
                    if abiStatic elem then
                      refLeafRegionFuel fuel' data
                        (elementsBlockStart + i * abiStaticBytes elem) elem rest
                    else
                      match refDynamicElementBlock data elementsBlockStart i with
                      | none => .overflow
                      | some childBlockStart =>
                          refLeafRegionFuel fuel' data childBlockStart elem rest
                  else
                    .overflow
          | .abiEncoded inner =>
              match guardedWord data blockStart with
              | none => .overflow
              | some _ =>
                  refLeafRegionFuel fuel' data (blockStart + wordSize) inner path
          | .transparent child => refLeafRegionFuel fuel' data blockStart child path
          | _ => .overflow

def decoderFuel (_t : AbiTy) (path : List Nat) : Nat :=
  path.length + 64

def rolesTopLevelLeafRegion (data : Calldata) (t : AbiTy) (path : List Nat) :
    DecodeResult :=
  rolesLeafRegionFuel (decoderFuel t path) data selectorSize t path

def refTopLevelLeafRegion (data : Calldata) (t : AbiTy) (path : List Nat) :
    DecodeResult :=
  refLeafRegionFuel (decoderFuel t path) data selectorSize t path

end Benchmark.Cases.Zodiac.RolesDecoderFaithfulness
