# Article Review

status: fixed pending push

critical_findings:
- Benchmark branch links cannot resolve publicly until `usual-daocollateral-conservation` is pushed.

major_findings:
- Initial reproduction command cloned default branch and did not check out the proof branch.

resolution:
- Updated the article `VERIFY_COMMAND` to `git checkout usual-daocollateral-conservation` before running the Lean proof build.
- Article branch will be pushed only after benchmark branch exists, making `BENCHMARK_BLOB` source links reviewable.

evidence:
- `npm run build` passes in `lfglabs.dev`.

confidence: high
