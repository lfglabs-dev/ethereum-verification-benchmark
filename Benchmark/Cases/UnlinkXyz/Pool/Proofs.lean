/-
  Reference proof file for the `unlink_xyz/pool` case.

  Placeholder — promotion to `build_green` only requires the `Contract.lean`
  declaration to elaborate. Once the three blocked entry points land (see
  the `BLOCKED(verity#1760-nested-dynamic):` markers in Contract.lean), the
  first proof target will be the per-token conservation invariant across
  `deposit + adapterDeposit` under the assumed Poseidon / Permit2 /
  Lazy-IMT / Groth16 boundaries declared in `Specs.lean`.
-/
import Benchmark.Cases.UnlinkXyz.Pool.Contract

namespace Benchmark.Cases.UnlinkXyz.Pool

/-- The case is `scoped`, so the build-green target is the absence of
    elaboration errors in `Contract.lean`. -/
theorem unlinkPool_compiles : True := trivial

end Benchmark.Cases.UnlinkXyz.Pool
