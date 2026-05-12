import Contracts.Common

namespace Benchmark.Cases.Zama.ERC7984ConfidentialToken

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Verity model of the OpenZeppelin ERC-7984 Confidential Token.

  ERC-7984 is a confidential fungible token standard built on Zama's fhEVM.
  All balances and transfer amounts are encrypted as euint64 ciphertext handles
  using Fully Homomorphic Encryption. Since FHE is homomorphic, the arithmetic
  logic on ciphertexts is identical to plaintext — this model verifies the
  plaintext-equivalent logic.

  Key semantic differences from ERC-20:
  - Transfers with insufficient balance silently transfer 0 (no revert)
  - Uses operator model (time-bounded) instead of approve/allowance
  - All arithmetic is modular at 2^64 (euint64)
  - FHE.isInitialized gates transfers from uninitialized accounts

  Upstream: OpenZeppelin/openzeppelin-confidential-contracts (master)
  File: contracts/token/ERC7984/ERC7984.sol
  Depends on: contracts/utils/FHESafeMath.sol

  Framework-required simplifications (cannot be modeled in Verity):
  - euint64 modeled as Uint256 with explicit mod 2^64 arithmetic
    (FHE homomorphism guarantees logical equivalence)
  - FHE.select modeled as if/then/else (logically equivalent)
  - FHE.allow/allowThis (ACL) omitted — separate on-chain system for
    ciphertext access control, does not affect balance state
  - FHE.fromExternal + inputProof omitted — cryptographic proof verification
    at the fhEVM layer, not contract logic
  - Disclosure/decryption flow omitted — requires off-chain gateway interaction
  - ERC1363-style callbacks (AndCall variants) omitted — external contract calls
  - Events omitted — not modeled in Verity
  - FHE.isInitialized modeled via a separate boolean mapping (balanceInitialized)
    since uninitialized euint64 (zero handle) is distinct from an explicit zero value
-/

/-! ## Constants -/

-- 2^64: modulus for euint64 wrapping arithmetic
def UINT64_MOD : Uint256 := 18446744073709551616

/-! ## FHE arithmetic helpers

  These model the FHE library operations on euint64 values.
  FHE.add wraps at 2^64; FHE.sub wraps at 2^64.
  All inputs are assumed to be in [0, 2^64) range.
-/

-- Models FHE.add(euint64, euint64) — wrapping addition mod 2^64
def add64 (a b : Uint256) : Uint256 := (add a b) % UINT64_MOD

-- Models FHE.sub(euint64, euint64) — wrapping subtraction mod 2^64
def sub64 (a b : Uint256) : Uint256 := (sub a b) % UINT64_MOD

/-! ## FHESafeMath helpers

  These model FHESafeMath.tryIncrease and FHESafeMath.tryDecrease from
  contracts/utils/FHESafeMath.sol.

  tryIncrease(oldValue, delta):
    newValue = (oldValue + delta) mod 2^64
    success  = newValue >= oldValue  (overflow detection)
    updated  = success ? newValue : oldValue

  tryDecrease(oldValue, delta):
    success  = oldValue >= delta
    updated  = success ? (oldValue - delta) : oldValue
-/

def tryIncrease64 (oldValue delta : Uint256) : Bool × Uint256 :=
  let newValue := add64 oldValue delta
  if newValue >= oldValue then (true, newValue)
  else (false, oldValue)

def tryDecrease64 (oldValue delta : Uint256) : Bool × Uint256 :=
  if oldValue >= delta then (true, sub oldValue delta)
  else (false, oldValue)

/-! ## Contract -/

verity_contract ERC7984 where
  storage
    -- Encrypted total supply (euint64 in Solidity)
    totalSupply : Uint256 := slot 0
    -- Encrypted balances: mapping(address => euint64)
    balances : Address → Uint256 := slot 1
    -- Tracks FHE.isInitialized for each balance handle
    -- 0 = uninitialized (handle never written), nonzero = initialized
    balanceInitialized : Address → Uint256 := slot 2
    -- Nested operator mapping: mapping(holder => mapping(spender => uint48 expiry))
    operators : Address → Address → Uint256 := slot 3

  /-
    Models the transfer path: _transfer(from, to, amount) → _update(from, to, amount)
    where from != address(0) and to != address(0).

    Solidity (_update, from != 0 && to != 0 path):
      euint64 fromBalance = _balances[from];
      require(FHE.isInitialized(fromBalance), ERC7984ZeroBalance(from));
      (success, ptr) = FHESafeMath.tryDecrease(fromBalance, amount);
      _balances[from] = ptr;
      transferred = FHE.select(success, amount, FHE.asEuint64(0));
      ptr = FHE.add(_balances[to], transferred);
      _balances[to] = ptr;
  -/
  function transfer (sender : Address, recipient : Address, amount : Uint256) : Uint256 := do
    require (sender != zeroAddress) "ERC7984InvalidSender"
    require (recipient != zeroAddress) "ERC7984InvalidReceiver"

    let fromBalance ← getMapping balances sender
    let fromInit ← getMapping balanceInitialized sender
    require (fromInit != 0) "ERC7984ZeroBalance"

    let success := fromBalance >= amount
    let newFromBalance := ite success (sub fromBalance amount) fromBalance
    setMapping balances sender newFromBalance
    setMapping balanceInitialized sender 1

    let transferred := ite success amount 0

    let toBalance ← getMapping balances recipient
    let newToBalance := (add toBalance transferred) % 18446744073709551616
    setMapping balances recipient newToBalance
    setMapping balanceInitialized recipient 1

    return transferred

  /-
    Models confidentialTransferFrom: operator check + _transfer + _update.

    The operator expiry is read from the nested operator mapping using
    the current block timestamp, matching the Solidity isOperator view:
      function isOperator(address holder, address spender) public view returns (bool) {
          return holder == spender || block.timestamp <= _operators[holder][spender];
      }

    Solidity:
      require(isOperator(from, msg.sender), ERC7984UnauthorizedSpender(from, msg.sender));
      transferred = _transfer(from, to, amount);
  -/
  function transferFrom
      (holder : Address, recipient : Address, amount : Uint256, blockTimestamp : Uint256) : Uint256 := do
    let spender ← msgSender
    let expiry ← getMapping2 operators holder spender
    -- isOperator: holder == spender || block.timestamp <= _operators[holder][spender]
    require (holder == spender || blockTimestamp <= expiry) "ERC7984UnauthorizedSpender"

    require (holder != zeroAddress) "ERC7984InvalidSender"
    require (recipient != zeroAddress) "ERC7984InvalidReceiver"

    let fromBalance ← getMapping balances holder
    let fromInit ← getMapping balanceInitialized holder
    require (fromInit != 0) "ERC7984ZeroBalance"

    let success := fromBalance >= amount
    let newFromBalance := ite success (sub fromBalance amount) fromBalance
    setMapping balances holder newFromBalance
    setMapping balanceInitialized holder 1

    let transferred := ite success amount 0

    let toBalance ← getMapping balances recipient
    let newToBalance := (add toBalance transferred) % 18446744073709551616
    setMapping balances recipient newToBalance
    setMapping balanceInitialized recipient 1

    return transferred

  /-
    Models setOperator(operator, until).

    Solidity:
      function setOperator(address operator, uint48 until) public virtual {
          _setOperator(msg.sender, operator, until);
      }
      function _setOperator(address holder, address operator, uint48 until) internal {
          _operators[holder][operator] = until;
      }
  -/
  function setOperator (operator : Address, expiry : Uint256) : Unit := do
    let holder ← msgSender
    setMapping2 operators holder operator expiry

  /-
    Models the mint path: _mint(to, amount) → _update(address(0), to, amount).

    Solidity (_update, from == 0 path):
      (success, ptr) = FHESafeMath.tryIncrease(_totalSupply, amount);
      _totalSupply = ptr;
      transferred = FHE.select(success, amount, FHE.asEuint64(0));
      ptr = FHE.add(_balances[to], transferred);
      _balances[to] = ptr;
  -/
  -- NOTE: `to` is reserved by EvmYul's Yul notation, so the parameter is named
  -- `recipient` here; it still corresponds to the `to` argument of Solidity's
  -- `_mint(to, amount)` / `_update(address(0), to, amount)` path.
  function mint (recipient : Address, amount : Uint256) : Uint256 := do
    require (recipient != zeroAddress) "ERC7984InvalidReceiver"

    let currentSupply ← getStorage totalSupply
    let newSupplyCandidate := (add currentSupply amount) % 18446744073709551616
    let success := newSupplyCandidate >= currentSupply
    let newSupply := ite success newSupplyCandidate currentSupply
    setStorage totalSupply newSupply

    let transferred := ite success amount 0

    let toBalance ← getMapping balances recipient
    let newToBalance := (add toBalance transferred) % 18446744073709551616
    setMapping balances recipient newToBalance
    setMapping balanceInitialized recipient 1

    return transferred

  /-
    Models the burn path: _burn(from, amount) → _update(from, address(0), amount).

    Solidity (_update, to == 0 path):
      euint64 fromBalance = _balances[from];
      require(FHE.isInitialized(fromBalance), ERC7984ZeroBalance(from));
      (success, ptr) = FHESafeMath.tryDecrease(fromBalance, amount);
      _balances[from] = ptr;
      transferred = FHE.select(success, amount, FHE.asEuint64(0));
      ptr = FHE.sub(_totalSupply, transferred);
      _totalSupply = ptr;
  -/
  function burn (holder : Address, amount : Uint256) : Uint256 := do
    require (holder != zeroAddress) "ERC7984InvalidSender"

    let fromBalance ← getMapping balances holder
    let fromInit ← getMapping balanceInitialized holder
    require (fromInit != 0) "ERC7984ZeroBalance"

    let success := fromBalance >= amount
    let newFromBalance := ite success (sub fromBalance amount) fromBalance
    setMapping balances holder newFromBalance
    setMapping balanceInitialized holder 1

    let transferred := ite success amount 0

    let currentSupply ← getStorage totalSupply
    let newSupply := (sub currentSupply transferred) % 18446744073709551616
    setStorage totalSupply newSupply

    return transferred

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
