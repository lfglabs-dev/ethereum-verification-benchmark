# Phase 1 Research: Rootstock Flyover Quote Lifecycle

## Protocol summary

Rootstock Flyover is a liquidity-provider protocol that accelerates Rootstock
peg-in and peg-out flows. The Liquidity Bridge Contract (LBC) stores signed
quotes between users and liquidity providers (LPs). For this benchmark the unit
of value at risk is the required RBTC quote amount held by `PegOutContract`
after `depositPegOut`: `quote.value + quote.callFee + quote.gasFee`. Dust
surplus below `dustThreshold` may remain in the contract and is deliberately
outside this per-quote settlement invariant. The target contract is
`src/PegOutContract.sol` at `rsksmart/liquidity-bridge-contract` commit
`88a6d1ad64aeb3ad24e01042f4211ad8649784b9`; the target functions are
`depositPegOut`, `refundPegOut`, `refundUserPegOut`, and the internal fallback
balance path through `_increaseBalance`.

Sources:

- LBC source repository:
  `https://github.com/rsksmart/liquidity-bridge-contract`
- Target source file:
  `https://github.com/rsksmart/liquidity-bridge-contract/blob/88a6d1ad64aeb3ad24e01042f4211ad8649784b9/src/PegOutContract.sol`
- Flyover / PPA protocol context:
  `https://ips.rootstock.io/IPs/RSKIP176.html`
- Rootstock Flyover overview:
  `https://medium.com/rootstock-tech-blog/the-flyover-protocol-7052708f16ce`

## Candidate invariants

1. Quote lifecycle conservation and single settlement for peg-out quotes. For a
   quote hash, once `depositPegOut` registers the quote, a successful
   `refundPegOut` or `refundUserPegOut` completes it and assigns the registered
   Rootstock-side amount exactly once: either to the LP/user transfer path or to
   `_balances` if the transfer fails. Any collateral slash call is separate
   explicit penalty accounting.
2. Duplicate quote settlement rejection. A quote with
   `_pegOutRegistry[quoteHash].completed == true` must not settle again through
   either refund function.
3. Required amount registration. `depositPegOut` must register only quotes whose
   received RBTC covers `quote.value + quote.callFee + quote.gasFee`, and the
   stored quote amount used later is that required amount rather than dust
   change.
4. Bitcoin transaction validation soundness. `refundPegOut` should accept only
   transactions whose OP_RETURN quote hash, destination address, amount, and
   confirmations match the quote. This is important but requires a broader model
   of Bitcoin serialization and the Rootstock bridge precompile.

The selected invariant is candidate 1 plus candidate 3 because it exercises the
compact lifecycle proposed in the task context, stays inside Solidity storage
and value accounting, and avoids modeling Powpeg/bridge internals.

## Evaluation of the proposed invariant

The user-proposed invariant is valid and well-targeted for `PegOutContract`.
The exact wording spans deposit, LP refund, user refund, bridge registration,
slashing call inputs, and fallback internal balances. For the first benchmark slice,
`PegOutContract` is sufficient: `depositPegOut`, `refundPegOut`, and
`refundUserPegOut` expose the accepted quote, settlement, collateral slash call,
completion flag, and fallback balance behavior. `PegInContract` can be a later
extension if the benchmark needs bridge registration coverage, but adding it
would mix two lifecycles and weaken the proof focus.

## Translation fidelity audit

| Solidity construct | Path / snippet | Closest Verity surface | Classification | Syntax or semantic risk |
| --- | --- | --- | --- | --- |
| `mapping(bytes32 => Quotes.PegOutQuote) _pegOutQuotes` | `src/PegOutContract.sol` storage | `quoteAmount : Address -> Uint256`, `quotePenalty : Address -> Uint256` | scoped simplification | `bytes32` key represented by `Address`; semantic risk limited to quote identity, not accounting |
| `mapping(bytes32 => PegOutRecord) _pegOutRegistry` | `completed`, `depositTimestamp` | `quoteCompleted : Address -> Uint256`, `quoteDepositTimestamp : Address -> Uint256` | no issue | Timestamp is retained for the LP penalty timing predicate |
| `mapping(address => uint256) _balances` | fallback balance for failed calls | `internalBalance : Address -> Uint256` keyed by recipient | no issue | Matches Solidity recipient-keyed additive balance |
| `quote.lbcAddress != address(0)` existence check | both refund functions | `quoteRegistered : Address -> Uint256` | no issue | Separate registered flag avoids treating zero amount as quote absence |
| `requiredAmount = quote.value + quote.callFee + quote.gasFee` | `depositPegOut` | guarded `add (add value callFee) gasFee` | no issue | Solidity 0.8 overflow reverts are modeled with explicit no-overflow guards before each addition |
| change refund when `msg.value - requiredAmount >= dustThreshold` | `depositPegOut` | `changeRefundSucceeds` branch | proof boundary | Failed change refund reverts; successful or below-dust deposits continue to registration |
| signature and quote hash validation | `_hashPegOutQuoteEIP712`, `_hashPegOutQuote` | success preconditions | hard blocker for full cryptographic proof | Out of scope for quote accounting |
| provider registration | `_collateralManagement.isRegistered` | success precondition | proof-gap-only | External registry call does not change quote amount |
| Bitcoin parsing and bridge confirmations | `_validatePegOutTransaction`, `_validateBtcTxConfirmations` | success precondition | hard blocker for this case | Requires BTC serialization and Bridge precompile semantics |
| `_pegOutRegistry[quoteHash].completed = true` | both refund functions | `setMapping quoteCompleted quoteHash completedFlag` | no issue | Direct storage write |
| `delete _pegOutQuotes[quoteHash]` | both refund functions | `setMapping quoteAmount quoteHash 0` | no issue | Accounting fields cleared explicitly |
| external RBTC calls | `addr.call{value: amount}` | `transferSucceeds : Bool` branch | proof boundary | Preserves branch: either paid or fallback balance credited; external callee behavior is not modeled |
| collateral slashing | `slashPegOutCollateral(...)` | `slashCallAmount := penalty` | proof boundary | Records the expected external call amount; does not prove CollateralManagement storage |

## Draft simplifications

- Quote hash modeled as an address-like key.
- Quote struct flattened to `value`, `callFee`, `gasFee`, and `penaltyFee`.
- External checks are successful-path preconditions, except LP penalty timing,
  which is computed from deposit timestamp, transfer allowance, BTC block time,
  first confirmation timestamp, expiry timestamp, and expiry block.
- External value transfer success is a Boolean branch.
- Fallback balances are recipient-keyed in the spec, matching Solidity
  `_balances[dest] += amount`.
- Quote existence is represented by `quoteRegistered`, not by nonzero amount.
- Deposit checked-addition overflow paths are explicit revert guards.

## Proposed Verity issues

None yet. Local package inspection is pending until `.lake/packages/verity` is
available in the clean worktree. The modeling choices above are benchmark
scoping decisions, not claims of missing Verity features.
