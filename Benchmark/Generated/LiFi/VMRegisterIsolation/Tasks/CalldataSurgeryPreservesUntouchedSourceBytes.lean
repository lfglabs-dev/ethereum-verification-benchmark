import Benchmark.Cases.LiFi.VMRegisterIsolation.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/--
`CALLDATA_SURGERY` preserves bytes in the source buffer outside the descriptor
union. A false `surgeryTouches` predicate models Solidity's `surgeryCount == 0`
no-op case.
-/
theorem calldata_surgery_preserves_untouched_source_bytes
    (s : VMState) (sourceReg : Nat) (touches : Nat -> Bool) (newBytes : Nat -> Nat) :
    let cmd : Command :=
      { op := Opcode.calldataSurgery, destReg := 0, sourceReg := sourceReg,
        outputBuffer := 0, surgeryTouches := touches, surgeryBytes := newBytes }
    let s' := step s cmd
    surgery_source_byte_frame_spec cmd s s' := by
  exact ?_

end Benchmark.Cases.LiFi.VMRegisterIsolation
