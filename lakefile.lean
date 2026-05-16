import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from git "https://github.com/lfglabs-dev/verity.git"@"820553c7f88e2b7605392a6f822ea373d029f3e3"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
