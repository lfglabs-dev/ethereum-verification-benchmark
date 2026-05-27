# Phase 1 - Research And Invariant Alignment

## Protocol Summary

Usual is an RWA-backed stablecoin protocol. USD0 is minted and redeemed against
eligible tokenized real-world assets through DaoCollateral. The target contract
is `src/daoCollateral/DaoCollateral.sol`, public proxy
`0xde6e1F680C4816446C8D515989E2358636A38b04`, active implementation
`0x0eEc861D49f15F585D6Bb4301FC4f89BCe22AF4e`. The unit of value at risk is
USD0 supply versus RWA collateral held by the treasury. No current exposure
snapshot is claimed in this phase. The selected functions are `swap`, `redeem`,
`_calculateFee`, `_burnStableTokenAndTransferCollateral`, and
`_getTokenAmountForAmountInUSD`.

Sources read:

- Usual USD0 DaoCollateral docs:
  https://tech.usual.money/smart-contracts/protocol-contracts/usd0/usd0-daocollateral
- Usual architecture docs:
  https://tech.usual.money/overview/architecture
- Usual USD0 fact sheet:
  https://docs.usual.money/resources-and-ecosystem/fact-sheets/usual-products/usd0
- Etherscan proxy:
  https://etherscan.io/address/0xde6e1F680C4816446C8D515989E2358636A38b04
- Etherscan implementation:
  https://etherscan.io/address/0x0eec861d49f15f585d6bb4301fc4f89bce22af4e#code
- Sourcify verified source:
  https://repo.sourcify.dev/contracts/partial_match/1/0x0eEc861D49f15F585D6Bb4301FC4f89BCe22AF4e/sources/src/daoCollateral/DaoCollateral.sol

## Candidate Invariants

1. Direct swap/redeem conservation. For successful direct swaps and redeems,
   ghosted USD0 supply effects and treasury collateral debits/credits match the
   source formulas, modulo configured redeem fee, oracle price, token decimals,
   CBR coefficient, and floor rounding.
2. Redeem returned-collateral formula. The collateral returned by redeem equals
   `floor((amount - fee) * tokenUnit / price)`, with CBR applying another
   floor multiplication by `cbrCoef / 1e18`.
3. Redeem fee formula. The fee equals `floor(amount * redeemFee / 10000)`,
   normalized through collateral token precision when token decimals are below
   USD0's 18 decimals.

Selected invariant: candidate 1, with candidates 2 and 3 as supporting proof
tasks. This is the minimum non-trivial invariant because it covers both sides
of the direct market: mint-on-collateral-in and burn-on-collateral-out.

## User-Proposed Invariant Evaluation

The proposed invariant is valid and well-targeted if it is kept to
DaoCollateral direct swap/redeem effects. It would be too broad if it tried to
prove USD0 token implementation correctness, oracle correctness, SwapperEngine
matching correctness, or treasury solvency outside the modeled direct paths.
The model therefore treats USD0 mint/burn and ERC20 transfers as ghosted effects
and verifies the DaoCollateral accounting equation itself.

## Translation Fidelity Audit

| Solidity construct | Closest Verity surface | Classification | Syntax/semantics risk |
| --- | --- | --- | --- |
| `swap(rwaToken, amount, minAmountOut)` | `swapDirect(rwaToken, amount, wadQuoteInUSD, minAmountOut)` | no issue | Oracle quote parameterized; same accounting writes. |
| `_calculateFee(amount, rwaToken)` | `redeemFeeAmount stableAmount redeemFee tokenUnit` | no issue | Preserves floor bps fee and token-decimal normalization. Sourcify source around line 500 shows `Math.mulDiv(usd0Amount, $.redeemFee, SCALAR_TEN_KWEI, Floor)` followed by token-decimal normalization. |
| `_burnStableTokenAndTransferCollateral(...)` | `redeemDirect` supply and collateral writes | no issue | ERC20/USD0 calls ghosted as supply/collateral state effects. |
| `_getTokenAmountForAmountInUSD` | `tokenAmountForUsd`, `cbrAdjustedTokenAmount` | no issue | Preserves floor oracle conversion and CBR branch. |
| Token mapping / registry / role checks / pause modifiers | omitted precondition gate | proof-gap-only | Affects call admissibility, not conservation arithmetic. |
| `Math.mulDiv(..., Floor)` | `floorMulDiv` | proof-gap-only | Overflow checks exposed as theorem preconditions. |
| SwapperEngine and intent functions | out of scope | no issue | User constraint says stay on DaoCollateral swap/redeem conservation. |

## Draft Simplifications

- Parameterize oracle quote, oracle price, and token unit.
- Model only direct swap/redeem paths.
- Ghost ERC20 transfer side effects as treasury collateral balance changes.
- Ghost USD0 mint/burn side effects as `usd0Supply` changes.
- Keep fee and CBR arithmetic because they are part of the conservation equation.

## Proposed Verity Issues

None. Local `.lake/packages/verity` contains support for the storage, mapping,
function, and proof style needed here. The simplifications are benchmark-scope
choices, not Verity blockers.
