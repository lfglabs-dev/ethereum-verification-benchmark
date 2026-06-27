import Lake
open Lake DSL

package «ethereum-verification-benchmark» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git" @
  "1fffe16c4fc910a7316d1dddc59dab5ab7fb1c8e"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
