import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git" @
  "06036b1f3b018068ca35769d8a64378c1fe6c8ae"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
