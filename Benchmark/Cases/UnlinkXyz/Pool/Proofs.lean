/-
  Reference proof file for the `unlink_xyz/pool` case.

  Placeholder — the `build_green` target requires the `Contract.lean`
  declaration to elaborate. The first proof target will likely be the
  per-token conservation invariant across `deposit + withdraw` under the
  explicit Poseidon / Permit2 / Groth16 boundaries declared in `Specs.lean`.
-/
import Benchmark.Cases.UnlinkXyz.Pool.Contract

namespace Benchmark.Cases.UnlinkXyz.Pool

/-- The case is `build_green`, so the task target is the absence of
    elaboration errors in `Contract.lean`. -/
theorem unlinkPool_compiles : True := trivial

end Benchmark.Cases.UnlinkXyz.Pool
