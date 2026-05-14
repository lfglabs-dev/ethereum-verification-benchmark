import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git"@"9ebe37665da81b2cf7af0b814e9c48661d4243f5"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
