import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from git "https://github.com/lfglabs-dev/verity.git"@"7ac455b22bf56c32245c35470abeaba03e3c88b7"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
