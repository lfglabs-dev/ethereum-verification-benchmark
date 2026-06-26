import Benchmark.Cases.LiFi.VMRegisterIsolation.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/--
`CALLDATA_SURGERY` preserves every register slot and can change only the byte
buffer currently addressed by `sourceReg.idx()`.
-/
theorem calldata_surgery_mutates_only_source_buffer
    (s : VMState) (sourceReg : Nat) (newBytes : Nat -> Nat) :
    let cmd : Command :=
      { op := Opcode.calldataSurgery, destReg := 0, sourceReg := sourceReg,
        outputBuffer := 0, surgeryTouches := fun _ => true,
        surgeryBytes := newBytes }
    let s' := step s cmd
    (∀ j, s'.slot j = s.slot j) ∧
      (∀ b, b ≠ readBufferId s sourceReg → s'.mem b = s.mem b) := by
  exact ?_

end Benchmark.Cases.LiFi.VMRegisterIsolation
