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
  - Uninitialized euint64 handles are handled inside FHESafeMath

  Upstream: OpenZeppelin/openzeppelin-confidential-contracts
  Commit: 83364738f0d2b1655c60627588e3493099c359f7
  File: contracts/token/ERC7984/ERC7984.sol
  Depends on: contracts/utils/FHESafeMath.sol

  Current scope/tooling simplifications:
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
  - FHE.isInitialized modeled via explicit initialized flags since an
    uninitialized euint64 handle is distinct from an explicit encrypted zero.
    Function arguments are modeled as initialized euint64 handles, so the
    FHESafeMath.tryDecrease branch for an uninitialized `delta` is outside
    this slice.
  - FHESafeMath and FHE.add/sub arithmetic is inlined in `_update`; the specs
    expose the same logic through named helper definitions for comparison.
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
    if oldValue is uninitialized:
      success = true
      updated = delta
    newValue = (oldValue + delta) mod 2^64
    success  = newValue >= oldValue  (overflow detection)
    updated  = success ? newValue : oldValue

  tryDecrease(oldValue, delta):
    if oldValue is uninitialized:
      success = delta == 0
      updated = 0
    success  = oldValue >= delta
    updated  = success ? (oldValue - delta) : oldValue
-/

def tryIncrease64SuccessWithInit (oldInit oldValue delta : Uint256) : Bool :=
  if oldInit == 0 then true
  else add64 oldValue delta >= oldValue

def tryIncrease64UpdatedWithInit (oldInit oldValue delta : Uint256) : Uint256 :=
  if oldInit == 0 then delta
  else
    let newValue := add64 oldValue delta
    if newValue >= oldValue then newValue else oldValue

def tryIncrease64WithInit (oldInit oldValue delta : Uint256) : Bool × Uint256 :=
  (tryIncrease64SuccessWithInit oldInit oldValue delta,
    tryIncrease64UpdatedWithInit oldInit oldValue delta)

def tryIncrease64 (oldValue delta : Uint256) : Bool × Uint256 :=
  tryIncrease64WithInit 1 oldValue delta

def tryDecrease64SuccessWithInit (oldInit oldValue delta : Uint256) : Bool :=
  if oldInit == 0 then
    delta == 0
  else oldValue >= delta

def tryDecrease64UpdatedWithInit (oldInit oldValue delta : Uint256) : Uint256 :=
  if oldInit == 0 then 0
  else if oldValue >= delta then sub oldValue delta
  else oldValue

def tryDecrease64WithInit (oldInit oldValue delta : Uint256) : Bool × Uint256 :=
  (tryDecrease64SuccessWithInit oldInit oldValue delta,
    tryDecrease64UpdatedWithInit oldInit oldValue delta)

def tryDecrease64 (oldValue delta : Uint256) : Bool × Uint256 :=
  tryDecrease64WithInit 1 oldValue delta

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
    -- Tracks whether _totalSupply holds an initialized euint64 handle.
    totalSupplyInitialized : Uint256 := slot 4

  /-
    Models Solidity `_update(from, to, amount)`.

    This mirrors the Solidity branches and uses helper-shaped models of
    `FHESafeMath.tryIncrease`, `FHESafeMath.tryDecrease`, `FHE.add`, and
    `FHE.sub`. The destination update is duplicated in the two source branches
    because current Verity source does not support the Solidity-like
    `if (...) { ... } else { ... }; shared tail` do-block shape.

    ACL calls (`FHE.allow*`), transient allowances, and events are elided
    because they do not affect balance or supply accounting.
  -/
  function internal _update (src : Address, dst : Address, amount : Uint256) : Uint256 := do
    if src == zeroAddress then
      -- (success, ptr) = FHESafeMath.tryIncrease(_totalSupply, amount);
      let currentSupply ← getStorage totalSupply
      let supplyInit ← getStorage totalSupplyInitialized
      let newSupplyCandidate := (add currentSupply amount) % 18446744073709551616
      let success := ite (supplyInit == 0) true (newSupplyCandidate >= currentSupply)
      let ptr := ite (supplyInit == 0) amount
        (ite (newSupplyCandidate >= currentSupply) newSupplyCandidate currentSupply)
      setStorage totalSupply ptr
      setStorage totalSupplyInitialized 1

      -- transferred = FHE.select(success, amount, FHE.asEuint64(0));
      let transferred := ite success amount 0

      if dst == zeroAddress then
        -- ptr = FHE.sub(_totalSupply, transferred);
        let currentSupplyAfterMint ← getStorage totalSupply
        let supplyPtr := (sub currentSupplyAfterMint transferred) % 18446744073709551616
        setStorage totalSupply supplyPtr
        setStorage totalSupplyInitialized 1
      else
        -- ptr = FHE.add(_balances[to], transferred);
        let toBalance ← getMapping balances dst
        let toPtr := (add toBalance transferred) % 18446744073709551616
        setMapping balances dst toPtr
        setMapping balanceInitialized dst 1

      return transferred
    else
      -- (success, ptr) = FHESafeMath.tryDecrease(_balances[from], amount);
      let fromBalance ← getMapping balances src
      let fromInit ← getMapping balanceInitialized src
      let success := ite (fromInit == 0) (amount == 0) (fromBalance >= amount)
      let ptr := ite (fromInit == 0) 0
        (ite (fromBalance >= amount) (sub fromBalance amount) fromBalance)
      setMapping balances src ptr
      setMapping balanceInitialized src 1

      -- transferred = FHE.select(success, amount, FHE.asEuint64(0));
      let transferred := ite success amount 0

      if dst == zeroAddress then
        -- ptr = FHE.sub(_totalSupply, transferred);
        let currentSupply ← getStorage totalSupply
        let supplyPtr := (sub currentSupply transferred) % 18446744073709551616
        setStorage totalSupply supplyPtr
        setStorage totalSupplyInitialized 1
      else
        -- ptr = FHE.add(_balances[to], transferred);
        let toBalance ← getMapping balances dst
        let toPtr := (add toBalance transferred) % 18446744073709551616
        setMapping balances dst toPtr
        setMapping balanceInitialized dst 1

      return transferred

  /-
    Models Solidity `_transfer(from, to, amount)`: plaintext zero-address
    checks followed by `_update(from, to, amount)`.
  -/
  function internal _transfer (sender : Address, recipient : Address, amount : Uint256) : Uint256 := do
    require (sender != zeroAddress) "ERC7984InvalidSender"
    require (recipient != zeroAddress) "ERC7984InvalidReceiver"
    let transferred ← _update sender recipient amount
    return transferred

  /-
    Public benchmark wrapper for the ERC-7984 confidential transfer path.
    Solidity exposes `confidentialTransfer`; the accounting body delegates to
    `_transfer`.
  -/
  function transfer (sender : Address, recipient : Address, amount : Uint256) : Uint256 := do
    let transferred ← _transfer sender recipient amount
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

    let transferred ← _transfer holder recipient amount
    return transferred

  /-
    Models `_setOperator(holder, operator, until)`.

    Solidity:
      function _setOperator(address holder, address operator, uint48 until) internal {
          _operators[holder][operator] = until;
      }
  -/
  function internal _setOperator (holder : Address, operator : Address, expiry : Uint256) : Unit := do
    setMapping2 operators holder operator expiry

  /-
    Models setOperator(operator, until).

    Solidity:
      function setOperator(address operator, uint48 until) public virtual {
          _setOperator(msg.sender, operator, until);
      }
  -/
  function setOperator (operator : Address, expiry : Uint256) : Unit := do
    let holder ← msgSender
    _setOperator holder operator expiry

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
  function internal _mint (recipient : Address, amount : Uint256) : Uint256 := do
    require (recipient != zeroAddress) "ERC7984InvalidReceiver"
    let transferred ← _update zeroAddress recipient amount
    return transferred

  function mint (recipient : Address, amount : Uint256) : Uint256 := do
    let transferred ← _mint recipient amount
    return transferred

  /-
    Models the burn path: _burn(from, amount) → _update(from, address(0), amount).

    Solidity (_update, from != 0 and to == 0 path):
      euint64 fromBalance = _balances[from];
      (success, ptr) = FHESafeMath.tryDecrease(fromBalance, amount);
      _balances[from] = ptr;
      transferred = FHE.select(success, amount, FHE.asEuint64(0));
      ptr = FHE.sub(_totalSupply, transferred);
      _totalSupply = ptr;
  -/
  function internal _burn (holder : Address, amount : Uint256) : Uint256 := do
    require (holder != zeroAddress) "ERC7984InvalidSender"
    let transferred ← _update holder zeroAddress amount
    return transferred

  function burn (holder : Address, amount : Uint256) : Uint256 := do
    let transferred ← _burn holder amount
    return transferred

end Benchmark.Cases.Zama.ERC7984ConfidentialToken
