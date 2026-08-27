import Benchmark.Cases.Gearbox.BytecodeVersionIndex.Specs

namespace Benchmark.Cases.Gearbox.BytecodeVersionIndex

set_option autoImplicit false

/-- An empty `(contractType, version)` slot receives the hash and every source
version index is updated by the exact `max` equation in Solidity. -/
theorem allowContract_unoccupied_establishes_versionIndexCoherence
    (s : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version)
    (hHash : bytecodeHash ≠ 0)
    (hEmpty : s._allowedBytecodeHashes cType ver = 0) :
    ∃ s', _allowContract s bytecodeHash cType ver = some s' ∧
      freshAllowanceUpdatesVersionIndexesExactly
        s s' bytecodeHash cType ver := by
  refine ⟨_updateVersionInfo
      { s with
        _allowedBytecodeHashes := fun key version =>
          if key = cType then
            if version = ver then bytecodeHash
            else s._allowedBytecodeHashes key version
          else s._allowedBytecodeHashes key version }
      cType ver, ?_, ?_⟩
  · have hZeroNeHash : 0 ≠ bytecodeHash := Ne.symm hHash
    simp [_allowContract, hEmpty, hZeroNeHash]
  · simp [freshAllowanceUpdatesVersionIndexesExactly, versionIsRecorded,
      latestShortcutsAdvance, onlyExpectedStateChanges,
      expectedFreshAllowance, _updateVersionInfo]

/-- The first source branch is a storage no-op when the exact hash is already
allowed for the requested type and version. -/
theorem allowContract_sameHash_is_noop
    (s : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version)
    (hSame : s._allowedBytecodeHashes cType ver = bytecodeHash) :
    _allowContract s bytecodeHash cType ver = some s := by
  simp [_allowContract, hSame]

/-- A different nonzero hash already occupying the slot takes the source revert
branch and performs no successful state transition. -/
theorem allowContract_differentHash_occupied_reverts
    (s : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version)
    (hDifferent : s._allowedBytecodeHashes cType ver ≠ bytecodeHash)
    (hOccupied : s._allowedBytecodeHashes cType ver ≠ 0) :
    _allowContract s bytecodeHash cType ver = none := by
  simp [_allowContract, hDifferent, hOccupied]

end Benchmark.Cases.Gearbox.BytecodeVersionIndex
