import Benchmark.Cases.Zodiac.RolesDecoderFaithfulness.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.Zodiac.RolesDecoderFaithfulness.Tasks

open Benchmark.Cases.Zodiac.RolesDecoderFaithfulness

theorem roles_decoder_bounds_safe_task
    (data : Calldata) (t : AbiTy) (path : List Nat) :
    roles_bounds_safe_spec data t path := by
  exact ?_

end Benchmark.Generated.Zodiac.RolesDecoderFaithfulness.Tasks
