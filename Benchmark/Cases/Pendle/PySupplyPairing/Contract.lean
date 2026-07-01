import Contracts.Common
import Verity.Stdlib.Math

namespace Benchmark.Cases.Pendle.PySupplyPairing

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Focused Verity slice of Pendle V2 PY mint/redeem accounting.

  Upstream: pendle-finance/pendle-core-v2-public
  Commit: e8c2cca4c9b329ba8a383a27d7318e5f8b35c843
  Files:
  - contracts/core/YieldContracts/PendleYieldToken.sol
  - contracts/core/YieldContracts/PendlePrincipalToken.sol
  - contracts/core/StandardizedYield/SYUtils.sol

  Modeled Solidity behavior:
  - `mintPY(receiverPT, receiverYT)` single-receiver path.
  - `_mintPY` computes one PY amount from floating SY and mints exactly that
    amount to YT and PT.
  - `redeemPY(receiver)` successful pre-expiry single-receiver path.
  - `_getAmountPYToRedeem` chooses min(PT held by this contract, YT held by
    this contract) before expiry.
  - `_redeemPY` burns both PT and YT before expiry.
  - `_pyIndexCurrent` stores max(exchangeRate, pyIndexStored) on mint. Redeem
    uses the same max expression for the returned SY amount, but the index
    storage write is elided because this case observes only PT/YT accounting.
  - `SYUtils.syToAsset` and `assetToSy` use the same floor-division formulas.

  Simplifications:
  - PT is inlined as paired storage inside this model. The real YT contract
    calls the trusted paired PT contract through `mintByYT` and `burnByYT`.
  - Multi-receiver `mintPYMulti` and `redeemPYMulti` are outside this case.
  - Rewards, user interest accrual, events, allowances, names/symbols/decimals,
    reentrancy status, and SafeERC20 return behavior are omitted because they do
    not affect PT/YT total supply pairing.
  - External SY transfers are represented by `syBalance`. Mint-side Solidity
    0.8 arithmetic paths use Verity checked arithmetic where the source can
    panic.
  - Redeem is modeled as a successful-path transition: source preconditions
    such as not expired, nonzero self address, sufficient PT/YT balances and
    supplies, uint248 fit, nonzero index, and no fixed-point multiplication
    overflow are theorem hypotheses. Under those preconditions the model
    performs the same PT/YT burns and returns the source-close `amountSyOut`.
  - `_pyIndexCurrent` source code narrows the stored index through `PMath.Uint128`;
    this source-side successful-path precondition is not modeled because the
    theorem observes only PT/YT supply and balance state.
  - YT `_beforeTokenTransfer` reward/interest hooks can execute during mint/burn;
    hook-side reverts and reward/index state updates are out of scope because
    they do not directly mutate the modeled PT/YT accounting state.
  - The Solidity redeem tail transfers SY, then updates SY reserve, but those
    operations cannot mutate PT or YT supply/balance state used by this case.
  - Post-expiry redeem is intentionally excluded because Pendle burns PT but not
    YT after maturity, so the selected pairing invariant is pre-expiry only.
-/

def ONE : Uint256 := 1000000000000000000

def uint248Max : Uint256 :=
  452312848583266388373324160190187140051835877600158453279131187530910662655

abbrev requireSomeUint := Verity.Stdlib.Math.requireSomeUint

abbrev safeAdd := Verity.Stdlib.Math.safeAdd

abbrev safeMul := Verity.Stdlib.Math.safeMul

abbrev safeDiv := Verity.Stdlib.Math.safeDiv

def syToAsset (exchangeRate syAmount : Uint256) : Uint256 :=
  div (mul syAmount exchangeRate) ONE

def assetToSy (exchangeRate assetAmount : Uint256) : Uint256 :=
  div (mul assetAmount ONE) exchangeRate

def maxUint (a b : Uint256) : Uint256 :=
  if a >= b then a else b

def minUint (a b : Uint256) : Uint256 :=
  if a <= b then a else b

def pyToRedeem (expiredFlag ptHeldByContract ytHeldByContract : Uint256) : Uint256 :=
  if expiredFlag == 0 then minUint ptHeldByContract ytHeldByContract else ptHeldByContract

verity_contract PendlePY where
  storage
    -- YT ERC20 `_totalSupply`.
    ytTotalSupply : Uint256 := slot 0
    -- PT ERC20 `_totalSupply`, inlined from the paired principal token.
    ptTotalSupply : Uint256 := slot 1
    -- YT ERC20 balances.
    ytBalances : Address → Uint256 := slot 2
    -- PT ERC20 balances.
    ptBalances : Address → Uint256 := slot 3
    -- `PendleYieldToken.syReserve`.
    syReserve : Uint256 := slot 4
    -- Modeled SY token balance held by the YT contract.
    syBalance : Uint256 := slot 5
    -- `PendleYieldToken._pyIndexStored`.
    pyIndexStored : Uint256 := slot 6
    -- Modeled `IStandardizedYield(SY).exchangeRate()`.
    exchangeRate : Uint256 := slot 7
    -- 0 means not expired, nonzero means expired.
    expired : Uint256 := slot 8
    -- Post-expiry treasury interest accumulator, retained for branch shape.
    postExpiryTreasuryInterest : Uint256 := slot 9

  function internal _currentIndex () : Uint256 := do
    let rate ← getStorage exchangeRate
    let stored ← getStorage pyIndexStored
    let current := maxUint rate stored
    setStorage pyIndexStored current
    return current

  function internal _mintYT (account : Address, amount : Uint256) : Unit := do
    require (account != zeroAddress) "ERC20: mint to the zero address"

    let oldSupply ← getStorage ytTotalSupply
    let oldBalance ← getMapping ytBalances account
    require (amount <= 452312848583266388373324160190187140051835877600158453279131187530910662655) "uint248 overflow"
    let newSupply ← requireSomeUint (safeAdd oldSupply amount) "Panic(0x11): arithmetic overflow"
    let newBalance ← requireSomeUint (safeAdd oldBalance amount) "Panic(0x11): arithmetic overflow"

    setStorage ytTotalSupply newSupply
    setMapping ytBalances account newBalance

  function internal _mintPT (account : Address, amount : Uint256) : Unit := do
    require (account != zeroAddress) "ERC20: mint to the zero address"

    let oldSupply ← getStorage ptTotalSupply
    let oldBalance ← getMapping ptBalances account
    require (amount <= 452312848583266388373324160190187140051835877600158453279131187530910662655) "uint248 overflow"
    let newSupply ← requireSomeUint (safeAdd oldSupply amount) "Panic(0x11): arithmetic overflow"
    let newBalance ← requireSomeUint (safeAdd oldBalance amount) "Panic(0x11): arithmetic overflow"

    setStorage ptTotalSupply newSupply
    setMapping ptBalances account newBalance

  function internal _burnYT (account : Address, amount : Uint256) : Unit := do
    require (account != zeroAddress) "ERC20: burn from the zero address"

    let oldSupply ← getStorage ytTotalSupply
    let oldBalance ← getMapping ytBalances account

    require (oldBalance >= amount) "ERC20: burn amount exceeds balance"
    require (amount <= 452312848583266388373324160190187140051835877600158453279131187530910662655) "uint248 overflow"
    require (oldSupply >= amount) "ERC20: burn amount exceeds total supply"

    setMapping ytBalances account (sub oldBalance amount)
    setStorage ytTotalSupply (sub oldSupply amount)

  function internal _burnPT (account : Address, amount : Uint256) : Unit := do
    require (account != zeroAddress) "ERC20: burn from the zero address"

    let oldSupply ← getStorage ptTotalSupply
    let oldBalance ← getMapping ptBalances account

    require (oldBalance >= amount) "ERC20: burn amount exceeds balance"
    require (amount <= 452312848583266388373324160190187140051835877600158453279131187530910662655) "uint248 overflow"
    require (oldSupply >= amount) "ERC20: burn amount exceeds total supply"

    setMapping ptBalances account (sub oldBalance amount)
    setStorage ptTotalSupply (sub oldSupply amount)

  function mintPY (receiverPT : Address, receiverYT : Address) : Uint256 := do
    let expiredFlag ← getStorage expired
    require (expiredFlag == 0) "YCExpired"

    let currentSyBalance ← getStorage syBalance
    let currentSyReserve ← getStorage syReserve
    require (currentSyBalance >= currentSyReserve) "YCSyReserveUnderflow"

    let floatingSy := sub currentSyBalance currentSyReserve
    require (floatingSy != 0) "YCNoFloatingSy"

    let rate ← getStorage exchangeRate
    let stored ← getStorage pyIndexStored
    let index := maxUint rate stored
    setStorage pyIndexStored index
    let scaledSy ← requireSomeUint (safeMul floatingSy index) "Panic(0x11): arithmetic overflow"
    let amountPYOut := div scaledSy 1000000000000000000

    _mintYT receiverYT amountPYOut
    _mintPT receiverPT amountPYOut

    -- `updateData` tail: `_updateSyReserve()`.
    setStorage syReserve currentSyBalance

    return amountPYOut

  function redeemPY (receiver : Address) : Uint256 := do
    let _receiverMarker := receiver
    let self ← contractAddress
    let ptHeldByContract ← getMapping ptBalances self
    let ytHeldByContract ← getMapping ytBalances self
    let amountPYToRedeem := ite (ptHeldByContract <= ytHeldByContract)
      ptHeldByContract
      ytHeldByContract

    let oldPtSupply ← getStorage ptTotalSupply
    let oldPtBalance ← getMapping ptBalances self
    let oldYtSupply ← getStorage ytTotalSupply
    let oldYtBalance ← getMapping ytBalances self

    let rate ← getStorage exchangeRate
    let stored ← getStorage pyIndexStored
    let index := maxUint rate stored
    let amountSyOut := div (mul amountPYToRedeem 1000000000000000000) index

    setMapping ptBalances self (sub oldPtBalance amountPYToRedeem)
    setStorage ptTotalSupply (sub oldPtSupply amountPYToRedeem)
    setMapping ytBalances self (sub oldYtBalance amountPYToRedeem)
    setStorage ytTotalSupply (sub oldYtSupply amountPYToRedeem)

    return amountSyOut

end Benchmark.Cases.Pendle.PySupplyPairing
