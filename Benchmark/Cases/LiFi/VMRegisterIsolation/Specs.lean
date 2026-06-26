import Benchmark.Cases.LiFi.VMRegisterIsolation.Contract

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/--
Register-slot isolation for one successful VM step.

If the command did not declare register `j` as its destination write, the
physical register slot `j` is byte-buffer-identical after the step.
-/
def slot_frame_spec (cmd : Command) (s s' : VMState) : Prop :=
  ∀ j, ¬ commandWritesSlot cmd j → s'.slot j = s.slot j

/--
Buffer isolation for one successful VM step.

Only `CALLDATA_SURGERY` can mutate an existing register buffer. The target
buffer is the buffer id currently stored in `sourceReg.idx()`.
-/
def buffer_frame_spec (cmd : Command) (s s' : VMState) : Prop :=
  ∀ b, ¬ commandWritesBuffer s cmd b → s'.mem b = s.mem b

/--
Void-register writes are no-ops. This mirrors `RegisterFile.set` and
`setDynamic`, which return immediately when the masked destination is 0x7A.
-/
def void_register_write_spec (rawReg _newBuffer : Nat) (s s' : VMState) : Prop :=
  idx rawReg = VOID_REG → s' = s

/--
Void-register reads return the zero byte abstraction. The real source returns
ABI-encoded `uint256(0)`; this byte-level model represents every observed byte
of that zero word as `ZERO_BYTE`.
-/
def void_register_read_spec (rawReg offset : Nat) (s : VMState) : Prop :=
  idx rawReg = VOID_REG → readRegByte s rawReg offset = ZERO_BYTE

/--
The scoped LI.FI VM register-isolation invariant: for each successful modeled
opcode, all non-target register slots and all non-target buffers are preserved.
-/
def scoped_opcode_frame_spec (cmd : Command) (s s' : VMState) : Prop :=
  slot_frame_spec cmd s s' ∧ buffer_frame_spec cmd s s'

/--
Surgery byte locality inside the source buffer: bytes outside the descriptor
union are unchanged. `surgeryTouches = fun _ => false` represents the Solidity
`surgeryCount == 0` no-op case.
-/
def surgery_source_byte_frame_spec (cmd : Command) (s s' : VMState) : Prop :=
  ∀ offset,
    cmd.surgeryTouches offset = false →
      s'.mem (readBufferId s cmd.sourceReg) offset =
        s.mem (readBufferId s cmd.sourceReg) offset

end Benchmark.Cases.LiFi.VMRegisterIsolation
