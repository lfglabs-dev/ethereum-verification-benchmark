import Contracts.Common

namespace Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused semantic model of Zama protocol-apps
  `contracts/confidential-wrapper/contracts/token/ERC7984Upgradeable.sol` at
  commit `2f88eef1d0b545438b1f74e21cdff7ea771805da`.

  Exact retained Solidity source and immutable provenance are stored under
  `cases/zama/erc7984_upgradeable_exact_source/upstream/`. This Lean module is
  not a line-by-line Solidity translation. It models the transfer-relevant
  `_update`, `_transfer`, and `confidentialTransfer` control flow, including the
  source's pre-write `FHE.isInitialized(fromBalance)` guard.

  Semantic boundaries:
  - encrypted `euint64` values are represented by plaintext `Uint256` values
    with explicit modulo-2^64 arithmetic;
  - FHE initialization is represented by a separate logical mapping;
  - one trusted Boolean represents the selected public overload's successful
    `FHE.fromExternal` input-proof or `FHE.isAllowed` wrapper predicate;
  - FHE ACL calls, events, callbacks, metadata, and ERC-7201 slot derivation are
    outside this transfer-accounting slice.
-/

/-- Modulus of the plaintext-equivalent `euint64` arithmetic. -/
def UINT64_MOD : Uint256 := 18446744073709551616

/-- Plaintext-equivalent `FHE.add(euint64, euint64)`. -/
def add64 (a b : Uint256) : Uint256 := (add a b) % UINT64_MOD

verity_contract ERC7984UpgradeableExact where
  storage
    -- Logical fields from `ERC7984Storage`; these are not physical ERC-7201 slots.
    totalSupply : Uint256 := slot 0
    balances : Address → Uint256 := slot 1
    balanceInitialized : Address → Uint256 := slot 2
    totalSupplyInitialized : Uint256 := slot 3

  /-
    Transfer-relevant model of Solidity `_update(from, to, amount)`.

    The critical exact-source ordering on the non-mint branch is preserved:
      fromBalance = $._balances[from];
      require(FHE.isInitialized(fromBalance), ERC7984ZeroBalance(from));
      (success, ptr) = FHESafeMath.tryDecrease(fromBalance, amount);
      $._balances[from] = ptr;

    The destination and total-supply branches mirror the source's accounting
    shape. Ciphertext ACL operations and event emission have no representation
    in `ContractState` and are intentionally omitted.
  -/
  function internal _update (src : Address, dst : Address, amount : Uint256) : Uint256 := do
    if src == zeroAddress then
      -- (success, ptr) = FHESafeMath.tryIncrease($._totalSupply, amount)
      let currentSupply ← getStorage totalSupply
      let supplyInit ← getStorage totalSupplyInitialized
      let newSupplyCandidate := (add currentSupply amount) % 18446744073709551616
      let success := ite (supplyInit == 0) true (newSupplyCandidate >= currentSupply)
      let ptr := ite (supplyInit == 0) amount
        (ite (newSupplyCandidate >= currentSupply) newSupplyCandidate currentSupply)
      setStorage totalSupply ptr
      setStorage totalSupplyInitialized 1

      let transferred := ite success amount 0
      if dst == zeroAddress then
        let supplyAfterMint ← getStorage totalSupply
        setStorage totalSupply ((sub supplyAfterMint transferred) % 18446744073709551616)
        setStorage totalSupplyInitialized 1
      else
        let toBalance ← getMapping balances dst
        setMapping balances dst ((add toBalance transferred) % 18446744073709551616)
        setMapping balanceInitialized dst 1
      return transferred
    else
      let fromBalance ← getMapping balances src
      let fromInit ← getMapping balanceInitialized src

      -- Exact source guard, before every write on the non-mint branch:
      -- require(FHE.isInitialized(fromBalance), ERC7984ZeroBalance(from));
      require (fromInit != 0) "ERC7984ZeroBalance"

      -- (success, ptr) = FHESafeMath.tryDecrease(fromBalance, amount)
      let success := fromBalance >= amount
      let ptr := ite success (sub fromBalance amount) fromBalance
      setMapping balances src ptr
      setMapping balanceInitialized src 1

      -- transferred = FHE.select(success, amount, FHE.asEuint64(0))
      let transferred := ite success amount 0
      if dst == zeroAddress then
        let currentSupply ← getStorage totalSupply
        setStorage totalSupply ((sub currentSupply transferred) % 18446744073709551616)
        setStorage totalSupplyInitialized 1
      else
        let toBalance ← getMapping balances dst
        setMapping balances dst ((add toBalance transferred) % 18446744073709551616)
        setMapping balanceInitialized dst 1
      return transferred

  /- Plaintext zero-address checks followed by `_update`. -/
  function internal _transfer (sender : Address, recipient : Address, amount : Uint256) : Uint256 := do
    require (sender != zeroAddress) "ERC7984InvalidSender"
    require (recipient != zeroAddress) "ERC7984InvalidReceiver"
    let transferred ← _update sender recipient amount
    return transferred

  /-
    Public confidential-transfer wrapper.

    `wrapperPreconditionsPassed` is a trusted abstraction of either successful
    `FHE.fromExternal(encryptedAmount, inputProof)` validation or the
    `FHE.isAllowed(amount, msg.sender)` guard, depending on the selected Solidity
    overload. The proof tasks explicitly require it to be true.
  -/
  function confidentialTransfer
      (sender : Address, recipient : Address, amount : Uint256,
        wrapperPreconditionsPassed : Bool) : Uint256 := do
    require wrapperPreconditionsPassed "ERC7984WrapperPreconditionFailed"
    let transferred ← _transfer sender recipient amount
    return transferred

end Benchmark.Cases.Zama.ERC7984UpgradeableExactSource
