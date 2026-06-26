import Benchmark.Cases.LiFi.VMRegisterIsolation.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/--
`SAFE_TRANSFER` may transfer external ERC20 value, but it does not write the VM
register file or any register-owned byte buffer.
-/
theorem safe_transfer_preserves_slots_and_buffers (s : VMState) :
    let cmd : Command :=
      { op := Opcode.safeTransfer, destReg := 0, sourceReg := 0,
        outputBuffer := 0, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 }
    let s' := step s cmd
    scoped_opcode_frame_spec cmd s s' := by
  exact ?_

end Benchmark.Cases.LiFi.VMRegisterIsolation
