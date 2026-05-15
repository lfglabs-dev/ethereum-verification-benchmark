import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git"@"551ab45c7c2fefcdac385946d22758ff3854c00c"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
