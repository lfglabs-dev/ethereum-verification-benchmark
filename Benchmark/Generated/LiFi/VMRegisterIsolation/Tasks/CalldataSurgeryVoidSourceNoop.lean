import Benchmark.Cases.LiFi.VMRegisterIsolation.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/--
`CALLDATA_SURGERY` with source register `0x7A` mutates only the local zero
bytes object returned by `RegisterFile.get`, so it is a no-op over modeled
register-owned buffers.
-/
theorem calldata_surgery_void_source_noop
    (s : VMState) (sourceReg : Nat) (touches : Nat -> Bool) (newBytes : Nat -> Nat)
    (hVoid : idx sourceReg = VOID_REG) :
    let cmd : Command :=
      { op := Opcode.calldataSurgery, destReg := 0, sourceReg := sourceReg,
        outputBuffer := 0, surgeryTouches := touches, surgeryBytes := newBytes }
    let s' := step s cmd
    s' = s := by
  exact ?_

end Benchmark.Cases.LiFi.VMRegisterIsolation
