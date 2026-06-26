import Benchmark.Cases.LiFi.VMRegisterIsolation.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/--
Every scoped successful LI.FI VM opcode preserves all register slots and byte
buffers outside the opcode's write target.
-/
theorem scoped_opcode_frame (cmd : Command) (s : VMState) :
    let s' := step s cmd
    scoped_opcode_frame_spec cmd s s' := by
  exact ?_

end Benchmark.Cases.LiFi.VMRegisterIsolation
