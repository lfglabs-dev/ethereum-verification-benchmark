import Benchmark.Cases.KPK.SharesSettlementAccounting.Specs

namespace Benchmark.Generated.KPK.SharesSettlementAccounting
open Benchmark.Cases.KPK.SharesSettlementAccounting

-- Agent-editable goal deliberately retains its hole. The complete reference
-- solution is settlement_accounting in the case Proofs module, registered in task YAML.
theorem settlement_accounting (env : Environment) (before after : State)
    (n : Nat) (approved rejected : List Nat) (asset : Verity.Address) (price : Nat)
    (wf : WellFormed env before n) (ext : ExternalApplicability env before)
    (hp : price < wordLimit)
    (ids : ∀ id, id ∈ approved ++ rejected → id < wordLimit)
    (h : processRequests env approved rejected asset price before = .ok ((), after)) :
    SettlementAccounting env before after n approved rejected asset price := by
  exact ?_
end Benchmark.Generated.KPK.SharesSettlementAccounting
