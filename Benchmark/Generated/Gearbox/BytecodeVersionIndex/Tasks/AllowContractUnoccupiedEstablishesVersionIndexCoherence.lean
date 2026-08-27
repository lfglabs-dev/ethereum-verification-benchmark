import Benchmark.Cases.Gearbox.BytecodeVersionIndex.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Gearbox.BytecodeVersionIndex

set_option autoImplicit false

theorem allowContract_unoccupied_establishes_versionIndexCoherence
    (s : BytecodeRepository) (bytecodeHash : BytecodeHash)
    (cType : ContractType) (ver : Version)
    (hHash : bytecodeHash ≠ 0)
    (hEmpty : s._allowedBytecodeHashes cType ver = 0) :
    ∃ s', _allowContract s bytecodeHash cType ver = some s' ∧
      freshAllowanceUpdatesVersionIndexesExactly
        s s' bytecodeHash cType ver := by
  exact ?_
