import Benchmark.Cases.LiFi.VMRegisterIsolation.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/--
The all-false touch predicate models `surgeryCount == 0`, so surgery leaves the
source buffer bytes unchanged.
-/
theorem calldata_surgery_zero_count_noop
    (s : VMState) (sourceReg : Nat) (newBytes : Nat -> Nat) :
    let cmd : Command :=
      { op := Opcode.calldataSurgery, destReg := 0, sourceReg := sourceReg,
        outputBuffer := 0, surgeryTouches := fun _ => false,
        surgeryBytes := newBytes }
    let s' := step s cmd
    ∀ offset,
      s'.mem (readBufferId s sourceReg) offset =
        s.mem (readBufferId s sourceReg) offset := by
  exact ?_

end Benchmark.Cases.LiFi.VMRegisterIsolation
