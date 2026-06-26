namespace Benchmark.Cases.LiFi.VMRegisterIsolation

/-
  Focused benchmark model of LI.FI Composer's VirtualMachine register isolation
  surface.

  Source of truth:
  - Sourcify exact/perfect verified source for
    0xb57Ce43Be47DF611C98EB0943e5D36EBDb36cc6D on Base chain 8453.
  - Local evidence copied in this mission under:
    .context/verity-prove-invariant/lifi-vm-register-isolation/source/sourcify-8453/

  Solidity files in scope:
  - src/VirtualMachine.sol
  - src/RegisterFile.sol
  - src/RegisterHelpers.sol
  - src/SurgeryOPS.sol
  - src/BlueprintEncoder.sol
  - src/DepositApproved.sol
  - src/SafeTransferLib.sol

  The source uses `RegisterHelpers.idx(r) = r & 0x7F`, so command bytes whose
  high bit differs address the same physical register. `RegisterFile` treats
  register 0x7A as the void register: reads return a zero word and writes are
  no-ops. `SurgeryOps.performSurgery` is intentionally different from ordinary
  register writes: it mutates the bytes buffer currently referenced by the
  source register in place.

  Simplifications
  ----------------
  What was simplified:
  - Solidity `bytes memory` values are represented by explicit buffer ids.
  Why:
  - The invariant is about alias-aware register isolation. Buffer ids make the
    aliasing that Solidity memory pointers can express visible to the proof.

  What was simplified:
  - Buffer contents are modeled as `Nat -> Nat` byte maps instead of bounded
    byte arrays.
  Why:
  - The frame theorem only needs to know which buffer can change. The exact
    right-aligned byte copy performed by `mstore8` is a separate byte-locality
    refinement and does not affect non-target buffer preservation.

  What was simplified:
  - External calls, ERC20 reads/transfers, `BlueprintEncoder`, `ABI_ENCODE`,
    and `DepositApproved` are summarized by their VM register effects.
  Why:
  - The scoped invariant is register-file isolation. These components may
    compute values or touch external token state, but they do not write VM
    registers except through the explicit destination write in
    `VirtualMachine._run`.

  What was simplified:
  - Reverts, command unpacking, gas, native balance, event logs, disabled
    `EXPLODE`, and `RETURN` output bytes are omitted from the successful-step
    frame model.
  Why:
  - Failed commands have no successful post-state. The benchmark targets the
    post-state frame condition for successful scoped commands.
-/

def VOID_REG : Nat := 122
def REG_MASK_SIZE : Nat := 128
def ZERO_BYTE : Nat := 0

def idx (raw : Nat) : Nat := raw % REG_MASK_SIZE

structure VMState where
  slot : Nat -> Nat
  mem : Nat -> Nat -> Nat

def setRegister (s : VMState) (rawReg newBuffer : Nat) : VMState :=
  if idx rawReg = VOID_REG then
    s
  else
    { s with slot := fun j => if j = idx rawReg then newBuffer else s.slot j }

def setBuffer (s : VMState) (bufferId : Nat) (newBytes : Nat -> Nat) : VMState :=
  { s with mem := fun b => if b = bufferId then newBytes else s.mem b }

def readBufferId (s : VMState) (rawReg : Nat) : Nat :=
  s.slot (idx rawReg)

def readRegByte (s : VMState) (rawReg offset : Nat) : Nat :=
  if idx rawReg = VOID_REG then ZERO_BYTE else s.mem (readBufferId s rawReg) offset

inductive Opcode where
  | call
  | calldataBuild
  | calldataSurgery
  | abiEncode
  | depositApproved
  | safeTransfer
deriving DecidableEq

structure Command where
  op : Opcode
  destReg : Nat
  sourceReg : Nat
  outputBuffer : Nat
  surgeryTouches : Nat -> Bool
  surgeryBytes : Nat -> Nat

def slotWriteTarget (cmd : Command) : Option Nat :=
  match cmd.op with
  | .call | .calldataBuild | .abiEncode | .depositApproved =>
      if idx cmd.destReg = VOID_REG then none else some (idx cmd.destReg)
  | .calldataSurgery | .safeTransfer => none

def bufferWriteTarget (s : VMState) (cmd : Command) : Option Nat :=
  match cmd.op with
  | .calldataSurgery =>
      if idx cmd.sourceReg = VOID_REG then none else some (readBufferId s cmd.sourceReg)
  | _ => none

def step (s : VMState) (cmd : Command) : VMState :=
  match cmd.op with
  | .call => setRegister s cmd.destReg cmd.outputBuffer
  | .calldataBuild => setRegister s cmd.destReg cmd.outputBuffer
  | .abiEncode => setRegister s cmd.destReg cmd.outputBuffer
  | .depositApproved => setRegister s cmd.destReg cmd.outputBuffer
  | .calldataSurgery =>
      if idx cmd.sourceReg = VOID_REG then
        s
      else
        let bufferId := readBufferId s cmd.sourceReg
        setBuffer s bufferId
          (fun offset =>
            if cmd.surgeryTouches offset then
              cmd.surgeryBytes offset
            else
              s.mem bufferId offset)
  | .safeTransfer => s

def run (s : VMState) : List Command -> VMState
  | [] => s
  | cmd :: rest => run (step s cmd) rest

def commandWritesSlot (cmd : Command) (j : Nat) : Prop :=
  slotWriteTarget cmd = some j

def commandWritesBuffer (s : VMState) (cmd : Command) (b : Nat) : Prop :=
  bufferWriteTarget s cmd = some b

def commandsWriteSlot : List Command -> Nat -> Prop
  | [], _ => False
  | cmd :: rest, j => commandWritesSlot cmd j ∨ commandsWriteSlot rest j

end Benchmark.Cases.LiFi.VMRegisterIsolation
