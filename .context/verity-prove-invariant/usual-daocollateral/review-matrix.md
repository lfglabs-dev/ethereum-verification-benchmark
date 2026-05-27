# Review Matrix

Reviewer missions were spawned through orchestrator `batch_create_workers` with
`backend: codex`, `model_override: gpt-5.5`, and `model_effort: high`.

| Phase | Reviewer | Status | Resolution |
| --- | --- | --- | --- |
| Research | Research Reviewer | fixed | Replaced `_transferFee` with `_calculateFee`; added Sourcify source evidence; stated no value-at-risk snapshot is claimed. |
| Research | Invariant Reviewer | fixed | Specs now use independent expected fee/return expressions; `swap_value_conservation` postcondition explicitly ties minted USD0 to `expectedSwapUsdQuote`; successful-call arithmetic hypotheses added. |
| Modelization | Modelization Reviewer | fixed | Added successful-call hypotheses for no-wrap arithmetic, fee/CBR bounds, nonzero quote, uint128 amount bound, and treasury collateral sufficiency; task metadata discloses these boundaries. |
| Modelization | Verity Reviewer | fixed | Verity macro limitations led to theorem-level preconditions rather than in-contract checked-arithmetic requires; targeted Contract/Specs/Proofs/Compile builds pass. |
| Modelization | Build Reviewer | fixed | Regenerated `benchmark-inventory.json` and `REPORT.md`; `validate_manifests.py` passes. |
| Proof | Proof Reviewer | pass with minor findings | `lake build Benchmark.Cases.Usual.DaoCollateral.Proofs` passes; no blocking proof issues. Generated task files intentionally remain `exact ?_` placeholders and are not reference proof artifacts. |
| Proof | Final Red Team Reviewer | pass with minor findings | Focused build, manifest validation, and reference-solution audit pass. Minor notes are scoped-claim boundaries: direct swap/redeem slice, ghosted ERC20/USD0 effects, parameterized oracle values, and successful-call arithmetic hypotheses. |
| Article | Article Reviewer | fixed pending push | Reproduction command now checks out `usual-daocollateral-conservation`; benchmark source links resolve after branch push. |
| Article | Final Red Team Reviewer rerun | pass with minor findings | Article proof table now lists the five `Proofs.lean` declarations and `Verify it yourself` appears immediately after the table. Minor notes are scoped-claim boundaries already disclosed in the article. |
