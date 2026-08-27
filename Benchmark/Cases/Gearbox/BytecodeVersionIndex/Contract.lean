import Contracts.Common

namespace Benchmark.Cases.Gearbox.BytecodeVersionIndex

/-!
# Gearbox BytecodeRepository version-index model

Pinned source: `gearbox-protocol/permissionless` commit
`b1b5e5bac7d2183a1f10c4bcc3d4bbf88c8b7769`,
`contracts/global/BytecodeRepository.sol`.

Storage corresponds to `VersionInfo` and the two mappings at lines 34-41 and
66-88. The modeled functions correspond to `_allowContract` (423-430),
`_updateVersionInfo` (591-599), `_getMajorVersion` (602-604), and
`_getMinorVersion` (607-609).

## Simplifications

* Solidity `bytes32` contract types and bytecode hashes, and `uint256` versions,
  are represented by `Nat`. Equality and the zero-hash sentinel are preserved.
  Version arithmetic uses natural modulo/subtraction; since `ver % n ≤ ver`,
  this agrees with successful Solidity unsigned arithmetic in both helpers.
* Solidity mappings are total Lean functions with the same default-value
  convention supplied by the input state. Functional updates preserve every
  key not written by the source functions.
* `EnumerableSet.UintSet` is represented by its membership function. The scoped
  property observes only `add(ver)`/`contains(ver)`, not enumeration order or
  the set's internal index array.
* `_allowContract` returns `Option BytecodeRepository`: `none` is the source
  revert for a different occupied hash, while `some s` is a successful return.
  Events are omitted because they do not affect repository storage.
* Owner, bytecode upload/audit records, domains, and removal are outside this
  internal-function slice. Its callers establish those guards before invoking
  `_allowContract`; none changes the four scoped writes.
-/

abbrev ContractType := Nat
abbrev BytecodeHash := Nat
abbrev Version := Nat

structure VersionInfo where
  owner : Nat
  latest : Version
  latestByMajor : Version → Version
  latestByMinor : Version → Version
  versionsSet : Version → Bool

structure BytecodeRepository where
  _allowedBytecodeHashes : ContractType → Version → BytecodeHash
  _versionInfo : ContractType → VersionInfo

/-- Source `_getMajorVersion`: retain the hundreds-and-above prefix. -/
def _getMajorVersion (ver : Version) : Version :=
  ver - ver % 100

/-- Source `_getMinorVersion`: retain the tens-and-above prefix. -/
def _getMinorVersion (ver : Version) : Version :=
  ver - ver % 10

/-- Source `_updateVersionInfo`, preserving all writes and max branches. -/
def _updateVersionInfo
    (s : BytecodeRepository) (cType : ContractType) (ver : Version) :
    BytecodeRepository :=
  let info := s._versionInfo cType
  let majorVersion := _getMajorVersion ver
  let minorVersion := _getMinorVersion ver
  let updatedInfo : VersionInfo :=
    { info with
      latest := max ver info.latest
      latestByMajor := fun key =>
        if key = majorVersion then max ver (info.latestByMajor majorVersion)
        else info.latestByMajor key
      latestByMinor := fun key =>
        if key = minorVersion then max ver (info.latestByMinor minorVersion)
        else info.latestByMinor key
      versionsSet := fun version =>
        if version = ver then true else info.versionsSet version }
  { s with
    _versionInfo := fun key =>
      if key = cType then updatedInfo else s._versionInfo key }

/--
Source `_allowContract`. A same-hash entry is a successful no-op; a different
nonzero entry reverts; an empty entry stores the hash then updates all version
indexes.
-/
def _allowContract
    (s : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version) : Option BytecodeRepository :=
  let current := s._allowedBytecodeHashes cType ver
  if current = bytecodeHash then
    some s
  else if current ≠ 0 then
    none
  else
    let withHash : BytecodeRepository :=
      { s with
        _allowedBytecodeHashes := fun key version =>
          if key = cType then
            if version = ver then bytecodeHash
            else s._allowedBytecodeHashes key version
          else s._allowedBytecodeHashes key version }
    some (_updateVersionInfo withHash cType ver)

end Benchmark.Cases.Gearbox.BytecodeVersionIndex
