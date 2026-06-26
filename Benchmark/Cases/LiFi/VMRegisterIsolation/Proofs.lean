import Benchmark.Cases.LiFi.VMRegisterIsolation.Specs

namespace Benchmark.Cases.LiFi.VMRegisterIsolation

theorem idx_lt (raw : Nat) : idx raw < REG_MASK_SIZE := by
  unfold idx REG_MASK_SIZE
  exact Nat.mod_lt raw (by decide)

theorem set_register_preserves_non_target_slots
    (s : VMState) (rawReg newBuffer j : Nat)
    (h : ¬ commandWritesSlot
      { op := Opcode.call, destReg := rawReg, sourceReg := 0,
        outputBuffer := newBuffer, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 } j) :
    (setRegister s rawReg newBuffer).slot j = s.slot j := by
  unfold setRegister
  by_cases hVoid : idx rawReg = VOID_REG
  · simp [hVoid]
  · by_cases hTarget : j = idx rawReg
    · subst j
      simp [commandWritesSlot, slotWriteTarget, hVoid] at h
    · simp [hVoid, hTarget]

theorem set_register_preserves_all_buffers
    (s : VMState) (rawReg newBuffer b : Nat) :
    (setRegister s rawReg newBuffer).mem b = s.mem b := by
  unfold setRegister
  by_cases hVoid : idx rawReg = VOID_REG
  · simp [hVoid]
  · simp [hVoid]

theorem set_buffer_preserves_all_slots
    (s : VMState) (bufferId : Nat) (newBytes : Nat -> Nat) (j : Nat) :
    (setBuffer s bufferId newBytes).slot j = s.slot j := by
  simp [setBuffer]

theorem set_buffer_preserves_non_target_buffers
    (s : VMState) (bufferId : Nat) (newBytes : Nat -> Nat) (b : Nat)
    (h : b ≠ bufferId) :
    (setBuffer s bufferId newBytes).mem b = s.mem b := by
  simp [setBuffer, h]

theorem void_register_write_noop
    (rawReg newBuffer : Nat) (s : VMState)
    (hVoid : idx rawReg = VOID_REG) :
    let s' := setRegister s rawReg newBuffer
    void_register_write_spec rawReg newBuffer s s' := by
  simp [void_register_write_spec, setRegister, hVoid]

theorem void_register_read_zero
    (rawReg offset : Nat) (s : VMState)
    (hVoid : idx rawReg = VOID_REG) :
    void_register_read_spec rawReg offset s := by
  simp [void_register_read_spec, readRegByte, hVoid, ZERO_BYTE]

theorem step_slot_frame (cmd : Command) (s : VMState) :
    let s' := step s cmd
    slot_frame_spec cmd s s' := by
  cases cmd with
  | mk op destReg sourceReg outputBuffer surgeryTouches surgeryBytes =>
    cases op
    case call =>
      dsimp [step, slot_frame_spec]
      intro j h
      exact set_register_preserves_non_target_slots s destReg outputBuffer j h
    case calldataBuild =>
      dsimp [step, slot_frame_spec]
      intro j h
      have hCall :
          ¬ commandWritesSlot
            { op := Opcode.call, destReg := destReg, sourceReg := 0,
              outputBuffer := outputBuffer, surgeryTouches := fun _ => false,
              surgeryBytes := fun _ => 0 } j := by
        simpa [commandWritesSlot, slotWriteTarget] using h
      exact set_register_preserves_non_target_slots s destReg outputBuffer j hCall
    case calldataSurgery =>
      dsimp [step, slot_frame_spec]
      intro j _h
      by_cases hVoid : idx sourceReg = VOID_REG
      · simp [hVoid]
      · simp [hVoid, setBuffer]
    case abiEncode =>
      dsimp [step, slot_frame_spec]
      intro j h
      have hCall :
          ¬ commandWritesSlot
            { op := Opcode.call, destReg := destReg, sourceReg := 0,
              outputBuffer := outputBuffer, surgeryTouches := fun _ => false,
              surgeryBytes := fun _ => 0 } j := by
        simpa [commandWritesSlot, slotWriteTarget] using h
      exact set_register_preserves_non_target_slots s destReg outputBuffer j hCall
    case depositApproved =>
      dsimp [step, slot_frame_spec]
      intro j h
      have hCall :
          ¬ commandWritesSlot
            { op := Opcode.call, destReg := destReg, sourceReg := 0,
              outputBuffer := outputBuffer, surgeryTouches := fun _ => false,
              surgeryBytes := fun _ => 0 } j := by
        simpa [commandWritesSlot, slotWriteTarget] using h
      exact set_register_preserves_non_target_slots s destReg outputBuffer j hCall
    case safeTransfer =>
      dsimp [step, slot_frame_spec]
      intro j _h
      rfl

theorem step_buffer_frame (cmd : Command) (s : VMState) :
    let s' := step s cmd
    buffer_frame_spec cmd s s' := by
  cases cmd with
  | mk op destReg sourceReg outputBuffer surgeryTouches surgeryBytes =>
    cases op
    case call =>
      dsimp [step, buffer_frame_spec]
      intro b _h
      exact set_register_preserves_all_buffers s destReg outputBuffer b
    case calldataBuild =>
      dsimp [step, buffer_frame_spec]
      intro b _h
      exact set_register_preserves_all_buffers s destReg outputBuffer b
    case calldataSurgery =>
      dsimp [step, buffer_frame_spec]
      intro b h
      by_cases hVoid : idx sourceReg = VOID_REG
      · simp [hVoid]
      · unfold commandWritesBuffer bufferWriteTarget readBufferId at h
        by_cases hTarget : b = s.slot (idx sourceReg)
        · subst b
          exfalso
          apply h
          simp [hVoid]
        · simp [hVoid, setBuffer, readBufferId, hTarget]
    case abiEncode =>
      dsimp [step, buffer_frame_spec]
      intro b _h
      exact set_register_preserves_all_buffers s destReg outputBuffer b
    case depositApproved =>
      dsimp [step, buffer_frame_spec]
      intro b _h
      exact set_register_preserves_all_buffers s destReg outputBuffer b
    case safeTransfer =>
      dsimp [step, buffer_frame_spec]
      intro b _h
      rfl

theorem scoped_opcode_frame (cmd : Command) (s : VMState) :
    let s' := step s cmd
    scoped_opcode_frame_spec cmd s s' := by
  constructor
  · exact step_slot_frame cmd s
  · exact step_buffer_frame cmd s

theorem safe_transfer_preserves_slots_and_buffers (s : VMState) :
    let cmd : Command :=
      { op := Opcode.safeTransfer, destReg := 0, sourceReg := 0,
        outputBuffer := 0, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 }
    let s' := step s cmd
    scoped_opcode_frame_spec cmd s s' := by
  exact scoped_opcode_frame
      { op := Opcode.safeTransfer, destReg := 0, sourceReg := 0,
        outputBuffer := 0, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 } s

theorem calldata_surgery_mutates_only_source_buffer
    (s : VMState) (sourceReg : Nat) (newBytes : Nat -> Nat) :
    let cmd : Command :=
      { op := Opcode.calldataSurgery, destReg := 0, sourceReg := sourceReg,
        outputBuffer := 0, surgeryTouches := fun _ => true,
        surgeryBytes := newBytes }
    let s' := step s cmd
    (∀ j, s'.slot j = s.slot j) ∧
      (∀ b, b ≠ readBufferId s sourceReg → s'.mem b = s.mem b) := by
  constructor
  · intro j
    by_cases hVoid : idx sourceReg = VOID_REG
    · simp [step, hVoid]
    · simp [step, hVoid, setBuffer]
  · intro b h
    by_cases hVoid : idx sourceReg = VOID_REG
    · simp [step, hVoid]
    · by_cases hTarget : b = s.slot (idx sourceReg)
      · exfalso
        apply h
        simp [readBufferId, hTarget]
      · simp [step, hVoid, setBuffer, readBufferId, hTarget]

theorem calldata_surgery_preserves_untouched_source_bytes
    (s : VMState) (sourceReg : Nat) (touches : Nat -> Bool) (newBytes : Nat -> Nat) :
    let cmd : Command :=
      { op := Opcode.calldataSurgery, destReg := 0, sourceReg := sourceReg,
        outputBuffer := 0, surgeryTouches := touches, surgeryBytes := newBytes }
    let s' := step s cmd
    surgery_source_byte_frame_spec cmd s s' := by
  dsimp [surgery_source_byte_frame_spec, step, setBuffer, readBufferId]
  by_cases hVoid : idx sourceReg = VOID_REG
  · simp [hVoid]
  intro offset hUntouched
  simp [hVoid, hUntouched]

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
  dsimp [step, setBuffer, readBufferId]
  by_cases hVoid : idx sourceReg = VOID_REG
  · simp [hVoid]
  intro offset
  simp [hVoid]

theorem calldata_surgery_void_source_noop
    (s : VMState) (sourceReg : Nat) (touches : Nat -> Bool) (newBytes : Nat -> Nat)
    (hVoid : idx sourceReg = VOID_REG) :
    let cmd : Command :=
      { op := Opcode.calldataSurgery, destReg := 0, sourceReg := sourceReg,
        outputBuffer := 0, surgeryTouches := touches, surgeryBytes := newBytes }
    let s' := step s cmd
    s' = s := by
  simp [step, hVoid]

theorem call_like_write_preserves_non_target_slots_and_all_buffers
    (s : VMState) (op : Opcode) (destReg outputBuffer : Nat)
    (hCallLike :
      op = Opcode.call ∨ op = Opcode.calldataBuild ∨
      op = Opcode.abiEncode ∨ op = Opcode.depositApproved) :
    let cmd : Command :=
      { op := op, destReg := destReg, sourceReg := 0,
        outputBuffer := outputBuffer, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 }
    let s' := step s cmd
    scoped_opcode_frame_spec cmd s s' := by
  rcases hCallLike with h | h | h | h
  · subst h
    exact scoped_opcode_frame
      { op := Opcode.call, destReg := destReg, sourceReg := 0,
        outputBuffer := outputBuffer, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 } s
  · subst h
    exact scoped_opcode_frame
      { op := Opcode.calldataBuild, destReg := destReg, sourceReg := 0,
        outputBuffer := outputBuffer, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 } s
  · subst h
    exact scoped_opcode_frame
      { op := Opcode.abiEncode, destReg := destReg, sourceReg := 0,
        outputBuffer := outputBuffer, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 } s
  · subst h
    exact scoped_opcode_frame
      { op := Opcode.depositApproved, destReg := destReg, sourceReg := 0,
        outputBuffer := outputBuffer, surgeryTouches := fun _ => false,
        surgeryBytes := fun _ => 0 } s

end Benchmark.Cases.LiFi.VMRegisterIsolation
