# Direct-deposit correspondence boundary

## What is checked

The existing business theorem is unchanged: a successful `runDirectDeposit` cannot
decrease backing slack. `source_success_refines` now relates an ordered list of
source-shaped checks and an independent, observed-balance endpoint construction to
that transition. `source_success_preservesBackingSlack` composes the results.

These are **handwritten Lean models**, not a Cairo interpreter, compiler
translation, or deployed-contract proof. `sourceChecks` exposes first failure order;
it does not execute callbacks or expose tentative writes to an external contract.
`Execution.lean` also interprets the phase effects in order: it enters the guard,
registers the account before global pause, installs observed custody, updates the
balance, and exits the guard. `ordered_eq_source` proves exact equivalence to the
endpoint model, including failure phase; `ordered_success_preservesBackingSlack`
then composes this with the original business theorem. Intermediate storage is not
exposed to external callbacks. Event/return serialization remains excluded.

`Storage.lean` models the amount/existence portion of a balance record, proves the
absent/create, existing/update and existing/remove branches agree with map addition,
and proves preservation of the record relation under checked updates. Registration
preserves that relation. `ReachableRecord` and its induction theorem establish the
invariant for local histories from empty records. They do not cover all protocol
writers. No felt decoder, storage address hashing, or linked-list pointer interpreter
has been verified.

## Source mapping and conditions

| Cairo location | Lean artifact | Boundary |
|---|---|---|
| `paraclear:2477–2513` | `sourceChecks`, `sourcePostState` | Both wrappers; caller/recipient identity must be faithfully encoded |
| `paraclear:3262–3272` | pause phase | Optional manager call; unconfigured manager is not called |
| `account:384–416` | registration phase; `registration_represents` | Set membership only, assuming valid nonzero account identities |
| `token:583–585` | global pause and decimals phases | One successful decimals read; reused for both conversions |
| `token:588–592`, `math:96–135` | amount/scaling phases | Decoded nonnegative felt input; i128 bounds; exponent ≤24 |
| `token:593–599` | allowance/support/registry phases | Registry configuration explicit; dispatch failures distinct from denial |
| `token:605–610` | balance/transfer/receipt phases | Checked subtraction precedes exact receipt comparison |
| `token:612–620` | credit and balance phases; `Storage.lean` | Valid decoded records and checked signed addition |
| `token:621–629` | event/exit phase markers | Event payload/returned felt and resource costs not interpreted |

At decimals >32, `get_scale_factor` reaches `pow_128` with exponent >24 and
reverts, including for zero amounts. The model bound therefore captures a runtime
failure, not only an invariant imported from asset registration.

An existing record must contain the queried token address and an i128-decodable
amount. An absent record must have amount zero. Otherwise source branching differs:
an absent record with stored amount 5 is replaced by 1 on a one-unit deposit, while
unconditional map addition would produce 6. This is a malformed-storage witness,
not an assertion that this state is reachable from the supplied implementation.

## External world relation still to discharge

For a concrete execution from world `W` to `W'`, the intended relation requires:

1. Every positive posted balance is represented exactly once in the account domain.
2. Concrete signed amounts and existence markers satisfy `StorageRepresents`.
3. Entry custody agrees with the token's actual accounting and the before-read.
   `ObservationsMatch` records this coupling, **not a source runtime check**.
4. All dispatcher statuses and returned values represent the actual calls. Amount,
   allowance, registry, token and caller/spender identities are correctly associated.
5. Calls before the sampled transfer and after the final balance observation do not
   change represented custody or balances. Intermediate calls do not mutate the
   snapshot-derived checks or balance used for the credit. Callbacks are excluded.
6. The normalization precision is fixed at both endpoints. Cairo itself reads
   decimals once. If modeled metadata is interpreted as live metadata, its endpoint
   consistency must also be established; no lifetime immutability is claimed.
7. Omitted operations (including account/list storage and event emission) complete
   for the concrete successful execution. Runtime/ABI/compiler semantics are trusted.

The missing theorem is:

```text
ConcreteRelation(W,s) ∧ EnvironmentalConditions(trace)
∧ CairoDeposit(W,calldata,trace) = success W'
→ ∃ input s', runSourceDeposit s input calls = ok s'
             ∧ ConcreteRelation(W',s')
```

Do not confuse that obligation with the proved `source_success_refines` between
Lean models. The latter does not define its premise to be successful Cairo execution.

The deposit guard does not protect the entire ABI: for example,
`execute_pending_transfers` (`paraclear:2035–2099`) changes balances under executor
authorization without entering the guard. It can invalidate a deposit-only frame
if called by an authorized external callee. No deployment role assignment was supplied.

## Failure semantics

`runSourceDeposit` returns the first rejected phase. `committedSourceState` restores
the input accounting projection on rejection and has a checked rollback lemma.
This wrapper assumes runtime rollback; it does not prove Starknet atomicity, nor
does it model fees, nonces, validation effects, caught nested failures, or gas/resource
exhaustion. No claim is made that every successful Lean run can execute on Cairo.

## Reproducible checks

`Compile` builds the ordered-execution/refinement/storage proofs, runs model regressions, and prints
their axiom dependencies. The regression corpus includes rounding, precision bounds,
negative/zero-crossing balances, registry failures, dispatcher failures, guard/pause
ordering, and receipt mismatches. These are Lean model tests, not Cairo execution.

```sh
lake build Benchmark.Cases.Paraclear.DirectDepositBacking.Compile
python3 -m unittest tests.test_paraclear_correspondence
python3 scripts/check_paraclear_correspondence.py --source-root /path/to/extraction --source-only
```

## Differential execution: integration pending

The supplied extraction lacks `Scarb.toml`, `Scarb.lock`, and the external registry,
Assets Manager and OpenZeppelin dependencies. Consequently this increment does not
claim any full-contract Cairo differential test has passed.

`Differential.lean` exports 49 JSONL fixtures and expected results from Lean, including
decimals 0/6/8/18/32/33, rounding boundaries, signed balance crossings, integer
overflows, unset registry, receipt mismatches, false transfer, and both wrappers.
All amounts use decimal strings to avoid JSON integer precision loss.

```sh
python3 scripts/check_paraclear_correspondence.py \
  --source-root /path/to/extraction --cairo-runner /path/to/private-cairo-adapter
```

The executable adapter receives `--source-root PATH` and JSONL records containing
only `id` and `input` on stdin. It must execute the **actual contract**, with mocks
for external contracts, using the original pinned dependencies. Initialize the
recipient balance/custody and other guards according to the fixture. Initialize the
recipient's account-registration marker as absent using test-only storage setup, even
when its balance record is present. This deliberately exercises account creation and
its rollback; these fixtures are not asserted to be reachable production histories. Use distinct
sender/recipient identities for `on_behalf=true`. Model test address `1` denotes the
recipient and selected token, not literal deployed addresses. For `decimals=33`,
use test-only storage setup or a token whose metadata changes after registration so
the deposit scaling path is actually tested. Never replace the deposit with a
handwritten Cairo copy. Supply maximum u256 allowance; enable global deposits and
token support, disable the Assets Manager, and permit registry transfers by default.

Return exactly one `{"id": ..., "result": ...}` per request, containing
`{"success": true_or_false, "custody_raw": "...", "recipient_balance": "...",
"registered": true_or_false, "guard_entered": false}`.
On rejection, report the actual post-revert storage and token observations: expected
custody/balance equal the input values and registration remains absent. Thus failed
calls after registration or transfer must demonstrate rollback, not just rejection.
The checker withholds expected results, rejects missing/duplicate IDs and mismatches,
and exits **2 (blocked)** if no runner was supplied. Source-only success explicitly
does not count as a differential execution pass. The fixture corpus is a baseline;
callback traces, failed-dispatch world rollback and malformed storage require
additional private integration tests before broader claims.

## Relationship to STRK20

The reusable ideas are explicit action/check structure, a separate refinement
theorem, and initial-state/preservation induction for representation invariants.
STRK20's transaction-to-sequential-action proofs are a methodological precedent,
not an available Cairo semantics bridge. The next substantial increment is to
discharge the concrete relation against pinned source/runtime semantics and external
implementations, not to add redundant backing theorems.
