import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git"@"1d6abc86b042dd99bea46b318452612e43b83839"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
