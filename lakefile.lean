import Lake
open Lake DSL

package «verity-benchmark» where
  version := v!"0.1.0"

require verity from git "https://github.com/lfglabs-dev/verity.git"@"0882797b7cafe64afc8133c3db8897b4c315e0ad"

@[default_target]
lean_lib «Benchmark» where
  globs := #[
    .one `Benchmark,
    .andSubmodules `Benchmark.Cases
  ]
