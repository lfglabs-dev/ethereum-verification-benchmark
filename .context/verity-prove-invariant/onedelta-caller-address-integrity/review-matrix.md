# Review Matrix

| Phase | Reviewer | Status | Findings | Resolution |
| --- | --- | --- | --- | --- |
| Research | Research Reviewer | pass_with_minor_findings | Scope wording should stay explicit: transfer-command pulls plus V3 direct callback shortcut, not repo-wide caller integrity. | Added explicit out-of-scope sentence in Phase 1. |
| Research | Invariant Reviewer | pass_with_minor_findings | Same scope caveat; V3 direct pull included and proven. | No blocking change required; wording clarified. |
| Modelization | Modelization Reviewer | pass_with_minor_findings | Prior blockers resolved; minor notes asked to align research wording with the final path-specific model and document callback proof expected-caller convention. | Updated Phase 1 audit wording and documented callback proofs as using a ghost expected-caller state anchor. |
| Modelization | Verity Reviewer | pass_with_minor_findings | `unsupported_feature_codes` metadata was abstraction wording, not real Verity unsupported features. | Changed `unsupported_feature_codes` to an empty list and kept abstractions in tags/notes. |
| Modelization | Build Reviewer | pass | Focused OneDelta targets, full `lake build`, and no-`sorry`/`axiom` scan all pass; only unrelated existing warnings remain. | No action required. |
| Proof | Proof Reviewer | pass | Phase 3 satisfies PROOF; proof target and full build pass; no local `sorry` or user-defined `axiom`; all ten generated tasks match reference declarations. | No action required. |
| Proof | Final Red Team Reviewer | pass | Prior manifest blockers fixed; manifest validation, focused OneDelta builds, full build, and scoped-claim review all pass. | No action required. |
| Article | Article Reviewer | blocked | Article structure/build/scoped claims passed, but initial links pointed to unpublished benchmark branch/main and stale docs paths; math view initially used friendly notation rather than `Specs.lean` names. | Updated math to use `Specs.lean` spec names, changed reproduction to build `Proofs`, updated docs paths, pointed benchmark links at branch, and pushed benchmark branch. Public links now return 200. |
| Article | Final Red Team Reviewer | blocked | Same public-branch blocker: benchmark links and `git checkout onedelta-caller-integrity` could not resolve before branch push. | Pushed `onedelta-caller-integrity`; branch and linked Proofs/case URLs now resolve publicly. |
