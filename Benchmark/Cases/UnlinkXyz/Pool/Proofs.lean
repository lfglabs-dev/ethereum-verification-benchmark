/-
  Reference proof file for the `unlink_xyz/pool` case.

  Placeholder — promotion to `build_green` only requires the `Contract.lean`
  declaration to elaborate. The first proof target will likely be the
  per-token conservation invariant across `deposit + withdraw` under the
  remaining Poseidon / Permit2 / Groth16 boundaries declared in `Specs.lean`.
-/
import Benchmark.Cases.UnlinkXyz.Pool.Contract

namespace Benchmark.Cases.UnlinkXyz.Pool

/-- The case is `scoped`, so the build-green target is the absence of
    elaboration errors in `Contract.lean`. -/
theorem unlinkPool_compiles : True := trivial

end Benchmark.Cases.UnlinkXyz.Pool
