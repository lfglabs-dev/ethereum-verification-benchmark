#!/usr/bin/env python3
"""Bounded KPK target checks. Uses caches; not a global Lake scheduler bound."""
from pathlib import Path
import os
import subprocess
import tempfile

root = Path(__file__).resolve().parents[3]
source = (root / 'lakefile.lean').read_text()
needle = '  version := v!"0.1.0"'
assert source.count(needle) == 1
config = source.replace(needle, needle + '\n  weakLeanArgs := #["-M", "3000", "-j", "1"]')
fd, name = tempfile.mkstemp(prefix='lakefile.kpk-verification-', suffix='.lean', dir=root)
try:
    with os.fdopen(fd, 'w') as f:
        f.write(config)
    # These are the same targets as lake build Benchmark.Cases.KPK.SharesSettlementAccounting.Proofs.
    for module in ['Proofs', 'Compile', 'Regression']:
        command = ['timeout', '--kill-after=5s', '170', 'lake', '-f', name,
                   'build', 'Benchmark.Cases.KPK.SharesSettlementAccounting.' + module]
        print(' '.join(command), flush=True)
        subprocess.run(command, cwd=root, check=True)
finally:
    for suffix in ['', '.olean', '.ilean']:
        Path(name + suffix).unlink(missing_ok=True)
