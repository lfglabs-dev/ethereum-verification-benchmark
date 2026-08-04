import Lake
open Lake DSL

package «ethereum-verification-benchmark» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git" @
  "0cb6b59b2e9a93c377280cc56610b5bd5e277bd3"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
