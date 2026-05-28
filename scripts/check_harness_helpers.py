#!/usr/bin/env python3
from __future__ import annotations

import json
import shutil
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.runners.grok_build import _json_or_raw_stdout
from scripts.check_run_artifacts import check_run


def main() -> int:
    errors: list[str] = []
    valid = json.loads(_json_or_raw_stdout('{"ok": true}'))
    if valid != {"ok": True}:
        errors.append("valid Grok JSON stdout was not preserved")
    malformed = json.loads(_json_or_raw_stdout("{not-json"))
    if malformed != {"raw_stdout": "{not-json"}:
        errors.append("malformed Grok stdout was not wrapped as raw_stdout")
    plain = json.loads(_json_or_raw_stdout("plain output"))
    if plain != {"raw_stdout": "plain output"}:
        errors.append("plain Grok stdout was not wrapped as raw_stdout")

    temp_root = Path(tempfile.mkdtemp(prefix="verity-artifact-helper-"))
    try:
        run_dir = temp_root / "run"
        (run_dir / "verifier").mkdir(parents=True)
        for rel in (
            "workspace-manifest.json",
            "harness-request.json",
            "harness-response.json",
            "stdout.txt",
            "stderr.txt",
            "report.md",
            "verifier/verifier.json",
        ):
            path = run_dir / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("{}\n", encoding="utf-8")
        (run_dir / "run.json").write_text("{bad-json\n", encoding="utf-8")
        artifact_errors = check_run(run_dir)
        if not artifact_errors or "run.json is not valid JSON" not in artifact_errors[0]:
            errors.append("artifact validator did not report malformed run.json cleanly")
    finally:
        shutil.rmtree(temp_root, ignore_errors=True)
    if errors:
        print("\n".join(errors))
        return 1
    print("harness helper checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
