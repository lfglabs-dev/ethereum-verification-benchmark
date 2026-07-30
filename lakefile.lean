import Lake
open Lake DSL

package «ethereum-verification-benchmark» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git" @
  "49105e54ceff6d66921572cc85583538c2c8497d"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
