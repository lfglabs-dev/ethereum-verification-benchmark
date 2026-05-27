# Phase 3 - Proof

Proof terminal condition: PROOF.

Target theorems:

- `direct_erc20_transferFrom_uses_outer_caller`
- `transfers_erc20_transferFrom_uses_outer_caller`
- `delta_compose_internal_erc20_transferFrom_uses_outer_caller`
- `direct_permit2_transferFrom_uses_outer_caller`
- `transfers_permit2_transferFrom_uses_outer_caller`
- `delta_compose_internal_permit2_transferFrom_uses_outer_caller`
- `flash_callback_erc20_transferFrom_uses_outer_caller`
- `swap_callback_permit2_transferFrom_uses_outer_caller`
- `v3_callback_direct_transferFrom_uses_outer_caller`
- `nested_flash_and_swap_callbacks_keep_outer_caller`

`lake build Benchmark.Cases.OneDelta.CallerAddressIntegrity.Proofs` succeeds.
No `sorry` or `axiom` appears in the OneDelta benchmark files.
