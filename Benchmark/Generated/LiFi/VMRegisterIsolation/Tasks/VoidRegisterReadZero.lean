import Benchmark.Cases.LiFi.VMRegisterIsolation.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/--
Reads from the LI.FI void register return the zero-byte abstraction.
-/
theorem void_register_read_zero
    (rawReg offset : Nat) (s : VMState)
    (hVoid : idx rawReg = VOID_REG) :
    void_register_read_spec rawReg offset s := by
  exact ?_

end Benchmark.Cases.LiFi.VMRegisterIsolation
