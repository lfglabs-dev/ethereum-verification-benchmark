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

/--
The exact storage transition established when `_allowContract` inserts a new,
nonzero hash into an empty `(contractType, version)` slot.

Exact `max` equations are intentional. Mere lower bounds would permit phantom
index values larger than every version ever accepted by the repository.
-/
def freshAllowanceUpdatesVersionIndexesExactly
    (before after : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version) : Prop :=
  after = expectedFreshAllowance before bytecodeHash cType ver ∧
    after._allowedBytecodeHashes cType ver = bytecodeHash ∧
    (after._versionInfo cType).versionsSet ver = true ∧
  (after._versionInfo cType).latest =
    max ver (before._versionInfo cType).latest ∧
  (after._versionInfo cType).latestByMajor (_getMajorVersion ver) =
    max ver ((before._versionInfo cType).latestByMajor (_getMajorVersion ver)) ∧
  (after._versionInfo cType).latestByMinor (_getMinorVersion ver) =
    max ver ((before._versionInfo cType).latestByMinor (_getMinorVersion ver))

end Benchmark.Cases.Gearbox.BytecodeVersionIndex
