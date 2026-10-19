import Benchmark.Cases.Taurus.CMTATPartialFreeze.Contract

namespace Benchmark.Cases.Taurus.CMTATPartialFreeze

/-- A successful ordinary entrypoint cannot instruct spending frozen tokens. -/
def senderProtected (before after : State) (op : Operation) : Prop :=
  op.amount.val ≤ balanceOf before op.sender - getFrozenTokens before op.sender ∧
  after.frozenTokens = before.frozenTokens ∧
  getFrozenTokens after op.sender ≤ balanceOf after op.sender ∧
  balanceOf after op.sender =
    if op.sender = op.recipient then balanceOf before op.sender
    else balanceOf before op.sender - op.amount.val

/-- Repeated-call claim is per-step sender protection, not global recipient backing. -/
def traceProtected : State → List Operation → Prop
  | _, [] => True
  | s, op :: tail =>
      match run s op with
      | .error _ => traceProtected s tail
      | .ok next => senderProtected s next op ∧ traceProtected next tail

/-- Separate authorized writer result; not part of ordinary frozen-map immutability. -/
def freezeBacking (after : State) (account : Verity.Core.Address) : Prop :=
  getFrozenTokens after account ≤ balanceOf after account

end Benchmark.Cases.Taurus.CMTATPartialFreeze
