import Benchmark.Cases.Gearbox.BytecodeVersionIndex.Contract

namespace Benchmark.Cases.Gearbox.BytecodeVersionIndex

/-- An independently written full expected post-state for the fresh branch.
The equality to this value supplies frame conditions for every unselected
mapping key, set membership, owner field, and version index. -/
def expectedFreshAllowance
    (before : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version) : BytecodeRepository :=
  let info := before._versionInfo cType
  {
    _allowedBytecodeHashes := fun key version =>
      if key = cType then
        if version = ver then bytecodeHash
        else before._allowedBytecodeHashes key version
      else before._allowedBytecodeHashes key version
    _versionInfo := fun key =>
      if key = cType then
        {
          owner := info.owner
          latest := max ver info.latest
          latestByMajor := fun major =>
            if major = _getMajorVersion ver then
              max ver (info.latestByMajor (_getMajorVersion ver))
            else info.latestByMajor major
          latestByMinor := fun minor =>
            if minor = _getMinorVersion ver then
              max ver (info.latestByMinor (_getMinorVersion ver))
            else info.latestByMinor minor
          versionsSet := fun version =>
            decide (version = ver) || info.versionsSet version
        }
      else before._versionInfo key
  }

/-- The new hash is stored and the inserted version is present in the version set. -/
def versionIsRecorded
    (after : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version) : Prop :=
  after._allowedBytecodeHashes cType ver = bytecodeHash ∧
    (after._versionInfo cType).versionsSet ver = true

/-- All three latest-version shortcuts move to the inserted version exactly when
it is newer. These are version numbers, not weights or scores. -/
def latestShortcutsAdvance
    (before after : BytecodeRepository) (cType : ContractType)
    (ver : Version) : Prop :=
  (after._versionInfo cType).latest =
      max ver (before._versionInfo cType).latest ∧
    (after._versionInfo cType).latestByMajor (_getMajorVersion ver) =
      max ver ((before._versionInfo cType).latestByMajor (_getMajorVersion ver)) ∧
    (after._versionInfo cType).latestByMinor (_getMinorVersion ver) =
      max ver ((before._versionInfo cType).latestByMinor (_getMinorVersion ver))

/-- The complete post-state is the independently specified expected state. This
is what guarantees that every unrelated modeled field and key stays unchanged. -/
def onlyExpectedStateChanges
    (before after : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version) : Prop :=
  after = expectedFreshAllowance before bytecodeHash cType ver

/--
The English guarantee for a fresh insertion, split into three named parts:
the version is recorded, all latest-version shortcuts advance exactly, and no
unrelated modeled state changes.
-/
def freshAllowanceUpdatesVersionIndexesExactly
    (before after : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version) : Prop :=
  versionIsRecorded after bytecodeHash cType ver ∧
    latestShortcutsAdvance before after cType ver ∧
    onlyExpectedStateChanges before after bytecodeHash cType ver

end Benchmark.Cases.Gearbox.BytecodeVersionIndex
