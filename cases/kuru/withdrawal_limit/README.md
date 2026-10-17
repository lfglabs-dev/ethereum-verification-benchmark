# Kuru V2 withdrawal policy

This case publishes an executable Lean semantic model, eight complete specification groups, and their reference proofs. The original Solidity is not distributed. Reproducing the Lean result does not require access to a private source repository.

## Guarantee

In the modeled system, successful ordinary withdrawals consume the one shared withdrawal credit exactly across accounts, tokens and transactions. A successful ordinary payout cannot reuse credit already consumed. The separate approved path does not consume the ordinary pools, but requires the designated authority and the root account owner's accepted signature for the exact instruction, with nonce, epoch and deadline checks and replay protection.

Credit consists of non-expired deposited value and a capped, refillable allowance. The batch conservation theorem explicitly requires a successful initial capacity observation. New deposits, expiry and configuration-dependent refill remain part of the model; this is not a timeless fixed-budget claim.

## Reproduce

From the repository root, using the pinned Lean/Verity toolchain:

```sh
lake build Benchmark.Cases.Kuru.WithdrawalLimit.Proofs
lake env lean -M 2400 Benchmark/Cases/Kuru/WithdrawalLimit/Proofs.lean
python3 scripts/validate_manifests.py
python3 scripts/check_reference_solutions.py
```

The reference proof prints the kernel dependencies of all eight groups and the combined theorem. Only the standard Lean foundations `propext`, `Classical.choice` and `Quot.sound` are used as applicable. There are no custom axioms or admitted reference proofs.

For constrained machines, run one module at a time, in this order: `HistoryProofs`, `ArithmeticProofs`, `CoreProofs`, `LimiterProofs`, `WriterProofs`, `Proofs`. Budget memory for the compiler and its supervisor; a direct Lean heap flag does not constrain a preceding Lake build. A build resource failure is not a passed proof.

The complete reference theorem is:

```lean
Benchmark.Cases.Kuru.WithdrawalLimit.policy_bundle : PolicyBundle
```

## Exact coverage

| Reference declaration | Complete proposition |
| --- | --- |
| `initialization_and_writer_closure` | Fresh initialization and every retained writer, including allocation, callbacks and transactions, preserve the combined reachable-state invariants. |
| `exact_history_correspondence` | Physical ring lookup and writes agree with chronological history, including inclusive 24-hour expiry, cache fallback, coalescing and wrap. |
| `valuation_and_widths` | Exact full-product rounding, dust, checked overflow, packing and narrowing-cast range safety. |
| `transaction_and_snapshots` | Lazy shared-history and price snapshots, reuse, transaction boundaries and rollback. |
| `ordinary_and_global_no_reuse` | Exact deposit credit, deposit-first consumption, conditional writes and list-inductive batch conservation on shared state. |
| `drip_and_configuration` | Capped refill, settlement under the old configuration, no instant grant or retroactive rate change, and flow locks. |
| `approved_authority_and_replay` | Authority and signed-instruction checkpoints, pre-transfer nonce consumption and callback-compatible replay exclusion. |
| `payout_coverage_and_atomicity` | Both payout paths, measured deposit credit and withdrawal settlement, checked refunds, persistent reentrancy guard, allowed callbacks and rollback. |

The Lean case is split by role. `Contract.lean` with `Contract/Limiter.lean` and `Contract/History.lean` is the model. `Specs.lean` is the specification. `Proofs.lean` and the five `Proofs/*Proofs.lean` modules are the complete reference proofs. `Tests/Regression.lean` contains supplemental finite model checks. `Compile.lean` is only the model/specification elaboration target, not a Solidity or Yul compiler result.

The eight generated task files deliberately end in `exact ?_`: they are agent-facing whole-group challenges, not the reference solutions. They are outside the reference proof import graph. `proof_status: complete` identifies the available complete reference proofs, not solved generated placeholders.

## Scope

The model uses Verity word/address types and explicit persistent/transient records. Its source/helper/storage/writer correspondence was reviewed manually. No Solidity-to-Lean, control-flow, storage-layout, compiler, Yul or bytecode refinement is mechanized; no deployment attestation or whole-exchange security claim is made.

The trace starts from fresh correctly initialized and bound proxies with unchanged implementations, fixed per-transaction timestamps and monotone new transactions. Populated-storage migrations and upgrades are excluded. Root/child allocation and list effects are concrete; non-custody exchange arithmetic and creation authorization use explicit in-range abstractions.

Signature acceptance is an external, model-defined interface bound to the exact owner, payload and domain. It is not a proof of cryptographic recovery, hashing or human assent. Price/role-provider answers, token observations and linked math-library correspondence have their documented external/manual boundaries.

ERC20 deposits credit the positive measured custody increase, bounded by the request. Both withdrawal paths reserve the requested maximum, pin the limiter's price and configuration before callbacks, and refund any request-minus-debit difference to the post-callback account balance using checked addition. Ordinary capacity is consumed afterward using the measured custody debit; an approved receipt retains the complete signed requested maximum separately from the actual debit. The measured settlement and credit obligations are included in the eighth specification group.

Payout accounting uses measured ERC20 custody debit and gross requested native payout, not recipient proceeds, exchange-rate fairness or net native loss. A native callback may return surplus without restoring spending credit. Supplied before/after token observations remain an external boundary: measuring a delta does not prove truthful balance reporting or automatic rebase reconciliation.

For source revision `62c478b05dfe936c87fa95f35d89307d4a2d303c`, independent modelization, proof, scoped-build and adversarial reviews accepted all eight specification groups and the combined policy result with no critical or major findings. The source revision is pinned in the case manifest without redistributing the original Solidity or exposing a private repository URL. The complete repository build remains incomplete under the bounded runner, and the Solidity/fork suites were not run for this update; finite model checks do not substitute for the universal Lean proofs.
