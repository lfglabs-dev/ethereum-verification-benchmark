# Tydro position-account floor and authority

## Source

- Public verified source: https://explorer.inkonchain.com/address/0xc3cd1e023a596066270E43Eb5399B1DB445D0286?tab=contract
- Verified source date: **2026-08-31**
- Compiler: Solidity `0.8.24`
- Deployment bundle: `TydroPositionAccountFactory` at
  `0xc3cd1e023a596066270E43Eb5399B1DB445D0286`, including
  `src/accounts/TydroPositionAccount.sol` and its imported helpers

SHA-256 hashes of the reviewed verified sources:

| Source file | SHA-256 |
|---|---|
| `TydroPositionAccount.sol` | `4946fc1dd0adf444fe0bde6b831e27a63c3c5deae0141caf39528d1866f11ec4` |
| `TydroPositionAccountValidation.sol` | `66fc1b68fafe9c2e646fba82b0ac52e1ddcb702d18e3413f88030d6311ee9807` |
| `TydroPositionIntentHashing.sol` | `5065ed00f02b9ddc4a4612ef12cf8cd6cf3feede716ffda17e91d132a15f57c0` |
| `TydroPositionTypes.sol` | `c139b9602dbffc72bfeeb083184a7728260dac3fa1dfb455b1bf348c0cfcc2aa` |

No upstream repository or commit is claimed for this explorer-verified bundle.

## Tasks

1. `open_enforces_signed_floors` — successful open enforces the signed swap-output,
   supplied-token, borrowed-token, and health-factor bounds.
2. `close_enforces_signed_floors` — successful close enforces the signed withdrawal,
   swap-output, remaining-debt, remaining-collateral, and unconditional health-factor bounds.
3. `lifecycle_success_requires_owner_authority` — lifecycle success binds clone identity,
   deadline, optional relayer, current nonce, and recovered immutable owner, then increments
   the nonce once.
4. `callback_success_requires_bound_context` — callback success requires the immutable Pool,
   account initiator, immutable borrow asset, and matching nonzero active context, consumed
   before effects.
5. `emode_success_requires_owner` — successful eMode mutation is owner-only.
6. `atoken_recovery_requires_owner` — successful aToken recovery is owner-only and pays owner.
7. `raw_supply_recovery_requires_owner` — successful raw supply-asset recovery is owner-only
   and pays owner.
8. `raw_borrow_recovery_requires_owner` — successful raw borrow-asset recovery is owner-only
   and pays owner.
9. `signed_open_success_respects_floor_and_authority` — stage composition derives the
   source `uint8` eMode-category bound from a successful modeled typing stage, then carries
   trusted digest/recovery premises through lifecycle authorization and all modeled open floors.
10. `signed_close_success_respects_floor_and_authority` — stage composition carries trusted
    digest/recovery premises through lifecycle authorization and all modeled close floors.

## Trust and scope boundaries

- The two signed open/close composition tasks are stage-composition theorems over the modeled
  lifecycle-authority and floor-check stages. They are not full refinements of ABI dispatch,
  public entry-point execution, Solidity control flow, or deployed bytecode.
- EIP-712 hashing and ECDSA recovery are represented by trusted digest functions and the
  supplied `recoveredSigner`; no cryptographic correctness or digest-injectivity claim is made.
- Aave, swap-route, token, and final Pool-settlement results are environment inputs. The
  floor theorems prove what successful source checks imply, not that those systems report
  economically correct values.
- Clone immutable arguments are pinned model inputs; ERC-1167 construction is not proved.
- Source EIP-1153 transient slots are explicit transaction-local model state. One-shot
  consumption order is preserved, but transient-storage bytecode refinement is out of scope.
- Multihop routing, registry oracle policy, events, and unrelated lifecycle behavior are
  excluded. The signed health-factor floor and measured swap-output floor remain distinct.
