# Research Review

status: fixed

critical_findings: none

major_findings:
- Reviewer found the benchmark named nonexistent helper `_transferFee`; deployed source uses `_calculateFee`.
- Reviewer requested either a sourced value-at-risk snapshot or an explicit statement that no current exposure snapshot is claimed.

resolution:
- Updated phase research, manifests, and task metadata to name `_calculateFee`.
- Added Sourcify source evidence for `_calculateFee`, `_getTokenAmountForAmountInUSD`, `_burnStableTokenAndTransferCollateral`, `swap`, and `redeem`.
- Documented that the research records accounting units, not a live exposure estimate.

evidence:
- Proxy `0xde6e1F680C4816446C8D515989E2358636A38b04` resolves to implementation `0x0eEc861D49f15F585D6Bb4301FC4f89BCe22AF4e`.
- Sourcify verified source: `src/daoCollateral/DaoCollateral.sol`.

confidence: high
