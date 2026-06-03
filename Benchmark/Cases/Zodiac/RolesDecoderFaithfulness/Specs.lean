import Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.Contract

namespace Benchmark.Cases.Zodiac.RolesDecoderFaithfulness

def metadata_bridge_spec (t : AbiTy) : Prop :=
  rolesIsInlined t = abiStatic t ∧
  (rolesIsInlined t = true → rolesInlinedSize t = abiStaticBytes t)

def bounds_safe_result (data : Calldata) (result : DecodeResult) : Prop :=
  match result with
  | .ok r => inBounds data r = true
  | .overflow => True

def roles_bounds_safe_spec (data : Calldata) (t : AbiTy) (path : List Nat) :
    Prop :=
  bounds_safe_result data (rolesTopLevelLeafRegion data t path)

def roles_ref_faithful_spec (data : Calldata) (t : AbiTy) (path : List Nat) :
    Prop :=
  rolesTopLevelLeafRegion data t path = refTopLevelLeafRegion data t path

def governed_field_agreement
    (data₁ data₂ : Calldata) (t : AbiTy) (path : List Nat) : Prop :=
  rolesTopLevelLeafRegion data₁ t path = rolesTopLevelLeafRegion data₂ t path

def canonical_injectivity_spec
    (data₁ data₂ : Calldata) (t : AbiTy) (path : List Nat) : Prop :=
  roles_ref_faithful_spec data₁ t path →
  roles_ref_faithful_spec data₂ t path →
  refTopLevelLeafRegion data₁ t path = refTopLevelLeafRegion data₂ t path →
  governed_field_agreement data₁ data₂ t path

end Benchmark.Cases.Zodiac.RolesDecoderFaithfulness
