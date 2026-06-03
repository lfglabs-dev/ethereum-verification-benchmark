| Reviewer | Status | Finding | Resolution |
| --- | --- | --- | --- |
| Research Reviewer | blocked | Metadata and article could overclaim completion/scope. | Updated metadata to proof complete and narrowed claims to public redeem arithmetic slice. |
| Research Reviewer | blocked | Need source citations for Solidity facts. | Added article links to `DECIMALS_OFFSET`, `redeem`, `_redeem`, `_convertToAssets`, and `WithdrawManager`. |
| Invariant Reviewer | blocked | Old split-bound task remained in generated tasks. | Removed generated task and YAML. |
| Invariant Reviewer | blocked | Need build confirmation and no `sorry`. | Targeted proof build passes and `rg` found no `sorry` or custom `axiom` in IPOR case files. |

Remaining global-build note:
`lake build` is running after the targeted proof passed. Any unrelated warnings
from existing benchmark cases should not be attributed to IPOR unless the build
fails after the IPOR modules.
