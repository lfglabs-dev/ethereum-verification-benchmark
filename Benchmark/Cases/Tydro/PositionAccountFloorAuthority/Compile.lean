import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Contract
import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Proofs

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

def caseReady : Bool := true

-- Terminal-proof audit: these declarations must have no custom or `sorry` axioms.
#print axioms open_enforces_signed_floors
#print axioms close_enforces_signed_floors
#print axioms lifecycle_success_requires_owner_authority
#print axioms open_typed_fields_are_source_bounded
#print axioms signed_open_success_respects_floor_and_authority
#print axioms signed_close_success_respects_floor_and_authority
#print axioms callback_success_requires_bound_context
#print axioms emode_success_requires_owner
#print axioms atoken_recovery_requires_owner
#print axioms raw_supply_recovery_requires_owner
#print axioms raw_borrow_recovery_requires_owner

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
