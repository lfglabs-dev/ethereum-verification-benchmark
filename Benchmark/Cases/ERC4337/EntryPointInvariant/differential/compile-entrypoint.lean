import Compiler.CompileDriver
import Benchmark.Cases.ERC4337.EntryPointInvariant.EntryPointV09

/-!
# Lean driver that emits Yul for `EntryPointV09`.

Invoked by `differential/run.sh` via `lake env lean --run`. Mirrors the
pattern in `lfglabs-dev/unlink-monorepo`'s
`script/verity/export-foundry-artifacts.sh`.

Args:
  args[0] — output directory for the Yul artifact
  args[1] — path to the ABI-adapter Yul library (overrides for IAccount,
            IPaymaster, IAggregator, IExec external calls)
-/

unsafe def main (args : List String) : IO Unit := do
  let outDir := args.headD "differential/build/yul"
  let externals := args.getD 1 ""
  Compiler.compileSpecsWithOptions
    [ Benchmark.Cases.ERC4337.EntryPointInvariant.EntryPointV09.spec ]
    outDir
    true
    [externals]
    {}
    none none none none
