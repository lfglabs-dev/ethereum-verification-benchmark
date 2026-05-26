# Review Matrix

| Phase | Reviewer | Status | Findings | Resolution |
| --- | --- | --- | --- | --- |
| Phase 1 | Research Reviewer | pass_with_minor_findings | Scope wording and docs citation improvements | Accepted. Research file now distinguishes curve-point storage consistency from reserve-token custody. |
| Phase 1 | Invariant Reviewer | pass_with_minor_findings | Lean spec is helper-alignment under `curveBalance`, not literal arithmetic deviation expression | Accepted. Research and article-facing language will use "corresponding to zero reserve-ratio deviation under the curveBalance abstraction." |
| Phase 2 | Modelization Reviewer | pass_with_minor_findings | Identity `curveBalance` was not faithful; missing caller branch and guards; axioms need terminal-result framing | Accepted. Model now uses opaque `curveBalance` plus computed helper inputs, adds caller/fee-router path modeling, restores nonzero/auth guards, and scopes init authority/alpha out of the invariant slice. Axioms remain explicit terminal results. |
| Phase 2 | Verity Reviewer | pass_with_minor_findings | Opaque helpers are unsupported in contract bodies, but ordinary supported `def` helpers work; storage/Uint issues are proof-work gaps | Accepted. Phase 2/3 notes now narrow the limitation claims. |
| Phase 2 | Build Reviewer | pass_with_minor_findings | Four Polaris targets built; full repo build was impractical under concurrent Lean jobs | Accepted. Focused build commands are recorded; full-repo build remains medium-confidence only. |
| Phase 3 | Proof Reviewer | pass_with_minor_findings | AXIOM terminal result acceptable; checked arithmetic wording should not imply complete fee arithmetic formalization | Accepted. Benchmark and article wording keep the result scoped to explicit axioms and successful-path assumptions. |
| Phase 3 | Final Red Team Reviewer | pass_with_minor_findings | Avoid bare "proved" wording; clarify open generated tasks versus complete AXIOM terminal result | Accepted. Case notes now state the terminal result is AXIOM and generated tasks are open challenge entrypoints. |
