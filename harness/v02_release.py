"""Reviewed, candidate-independent trust root for the frozen v0.2 release.

These literals are the v0.2 release TCB.  In particular, consumers must
compare candidate release metadata to these values before using a commit or
helper identity named by candidate JSON.  Updating this module is a reviewed
release operation, not a manifest regeneration operation.
"""
from __future__ import annotations

BASELINE_COMMIT = "c5a2344b121040445ccd745a3f839548ca8f9158"
# This is the one intentional pre-results environment migration for v0.2.  The
# task/reference source remains rooted at ``BASELINE_COMMIT`` below.
RELEASE_ENVIRONMENT = {
    "lean_toolchain": "leanprover/lean4:v4.24.0",
    "verity_rev": "49105e54ceff6d66921572cc85583538c2c8497d",
}
RELEASE_METADATA = {
    "benchmark": "ethereum-verification-benchmark",
    "benchmark_version": "0.2",
    "created_at": "2026-07-18",
    "git_sha": BASELINE_COMMIT,
    "manifest_schema_version": 1,
    "task_count": 240,
    "task_set_id": "sha256:ddfd5ad518a6cb840be16a04651f6d5db81690023dda9953250a70e6da8009fe",
    "harness_id": "sha256:244bbf5ca68050dd4a7e56bdb794a68bc01a74d169828039e0943e511f65f867",
    "environment_id": "sha256:63ba1672d2c275905329bcd2b7188d7a75eb3431492debccb5953ce4742ff41e",
    "mode": "fair",
    "budget": "normal",
}
RELEASE_SOURCE = {
    "commit": BASELINE_COMMIT,
    "entrypoint": "scripts/run_all.sh",
    "selector_command": "python3 harness/task_runner.py list --suite all",
    "selector_files_sha256": {
        "harness/task_runner.py": "0c19fc19dc4acd4dcc7b6e64504889b96e6340497291d51cf1774ac29e89858f",
        "scripts/run_all.sh": "53ffd5894f4e36beed583402e8d17d5d628032326fb74a4fe171477640bb8720",
    },
    "closure_helper": {
        "blob": "c6f1a35009258bbe209a4c2ee6ae01148127e858",
        "path": "scripts/v02_reference_closure.py",
        "sha256": "ec090173fd2555e2557e33fb88920ea9f1d83bf2aa1fa0bb971aa30c6c3937b2",
    },
}
