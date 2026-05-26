// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {ERC20Selectors} from "../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../shared/masks/Masks.sol";

// solhint-disable max-line-length

/**
 * @notice Lending base contract that wraps Silos (v2).
 */
abstract contract SiloV2Lending is ERC20Selectors, Masks {
    bytes32 private constant WITHDRAW = 0xb460af9400000000000000000000000000000000000000000000000000000000;
    bytes32 private constant WITHDRAW_WITH_COLLATERAL_TYPE = 0xb8337c2a00000000000000000000000000000000000000000000000000000000;

    bytes32 private constant REDEEM = 0xba08765200000000000000000000000000000000000000000000000000000000;
    bytes32 private constant REDEEM_WITH_COLLATERAL_TYPE = 0xda53766000000000000000000000000000000000000000000000000000000000;

    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 16             | amount                          |
     * | 16     | 20             | receiver                        |
     * | 36     | 20             | silo                            |
     */
    /// @notice Withdraw from lender given caller address
    function _withdrawFromSiloV2(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            let ptr := mload(0x40)
            // offset for amount at lower bytes
            let amountData := shr(128, calldataload(currentOffset))
            // receiver
            let receiver := shr(96, calldataload(add(currentOffset, 16)))

            let amount := and(UINT120_MASK, amountData)
            // get silo address
            let silo := shr(96, calldataload(add(currentOffset, 36)))
            // skip  to end
            currentOffset := add(currentOffset, 56)

            // collateral type
            let cType := and(UINT8_MASK, shr(120, amountData))

            // store common parameters
            mstore(add(ptr, 0x24), receiver)
            mstore(add(ptr, 0x44), callerAddress)

            // apply max if needed
            // use shares if maximum toggled
            switch amount
            case 0xffffffffffffffffffffffffffff {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add caller address as parameter
                mstore(0x04, callerAddress)
                // call to collateral token
                pop(staticcall(gas(), silo, 0x0, 0x24, 0x0, 0x20))
                // load the retrieved balance
                amount := mload(0x0)

                switch cType
                // 1 is the default non-protected collateral
                case 1 {
                    // selector redeem(uint256,address,address)
                    mstore(ptr, REDEEM)
                    mstore(add(ptr, 0x4), amount)
                    // common parameters here
                    // call silo
                    if iszero(call(gas(), silo, 0x0, ptr, 0x64, 0x0, 0x0)) {
                        returndatacopy(0x0, 0x0, returndatasize())
                        revert(0x0, returndatasize())
                    }
                }
                // others are id'ed by their enum
                default {
                    // selector redeem(uint256,address,address,uint256)
                    mstore(ptr, REDEEM_WITH_COLLATERAL_TYPE)
                    mstore(add(ptr, 0x4), amount)
                    // common parameters here
                    mstore(add(ptr, 0x64), cType)
                    // call silo
                    if iszero(call(gas(), silo, 0x0, ptr, 0x84, 0x0, 0x0)) {
                        returndatacopy(0x0, 0x0, returndatasize())
                        revert(0x0, returndatasize())
                    }
                }
            }
            default {
                switch cType
                // 1 is the default non-protected collateral
                case 1 {
                    // selector withdraw(uint256,address,address)
                    mstore(ptr, WITHDRAW)
                    mstore(add(ptr, 0x4), amount)
                    // common parameters here
                    // call silo
                    if iszero(call(gas(), silo, 0x0, ptr, 0x64, 0x0, 0x0)) {
                        returndatacopy(0x0, 0x0, returndatasize())
                        revert(0x0, returndatasize())
                    }
                }
                // others are id'ed by their enum
                default {
                    // selector withdraw(uint256,address,address,uint256)
                    mstore(ptr, WITHDRAW_WITH_COLLATERAL_TYPE)
                    mstore(add(ptr, 0x4), amount)
                    // common parameters here
                    mstore(add(ptr, 0x64), cType)
                    // call silo
                    if iszero(call(gas(), silo, 0x0, ptr, 0x84, 0x0, 0x0)) {
                        returndatacopy(0x0, 0x0, returndatasize())
                        revert(0x0, returndatasize())
                    }
                }
            }
        }
        return currentOffset;
    }

    bytes32 private constant BORROW = 0xd516418400000000000000000000000000000000000000000000000000000000;
    bytes32 private constant BORROW_SHARES = 0x889576f700000000000000000000000000000000000000000000000000000000;

    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 16             | amount                          |
     * | 16     | 20             | receiver                        |
     * | 36     | 20             | silo                            |
     */
    function _borrowFromSiloV2(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            // offset for amount at lower bytes
            let amountData := shr(128, calldataload(currentOffset))
            // receiver
            let receiver := shr(96, calldataload(add(currentOffset, 16)))
            // get silo
            let silo := shr(96, calldataload(add(currentOffset, 36)))
            // skip silo (end of data)
            currentOffset := add(currentOffset, 56)

            let amount := and(UINT120_MASK, amountData)

            let ptr := mload(0x40)

            // switch-case over borrow mode
            switch and(UINT8_MASK, shr(120, amountData))
            // by assets
            case 0 {
                // selector borrow(uint256,address,address)
                mstore(ptr, BORROW)
            }
            // by shares
            default {
                // selector borrowShares(uint256,address,address)
                mstore(ptr, BORROW_SHARES)
            }
            // the rest is he same for both cases
            mstore(add(ptr, 0x4), amount)
            mstore(add(ptr, 0x24), receiver)
            mstore(add(ptr, 0x44), callerAddress)

            // call silo
            if iszero(call(gas(), silo, 0x0, ptr, 0x64, 0x0, 0x0)) {
                returndatacopy(0x0, 0x0, returndatasize())
                revert(0x0, returndatasize())
            }
        }
        return currentOffset;
    }

    bytes32 private constant DEPOSIT = 0x6e553f6500000000000000000000000000000000000000000000000000000000;
    bytes32 private constant DEPOSIT_WITH_COLLATERAL_TYPE = 0xb7ec8d4b00000000000000000000000000000000000000000000000000000000;

    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | underlying                      |
     * | 20     | 16             | amount                          |
     * | 36     | 20             | receiver                        |
     * | 56     | 20             | silo                            |
     */
    /// @notice deposit to Silo
    function _depositToSiloV2(uint256 currentOffset) internal returns (uint256) {
        assembly {
            let underlying := shr(96, calldataload(currentOffset))
            // offset for amount at lower bytes
            let amountData := shr(128, calldataload(add(currentOffset, 20)))
            // receiver
            let receiver := shr(96, calldataload(add(currentOffset, 36)))
            // get silo
            let silo := shr(96, calldataload(add(currentOffset, 56)))
            // skip silo (end of data)
            currentOffset := add(currentOffset, 76)

            let amount := and(UINT120_MASK, amountData)
            // zero is this balance
            if iszero(amount) {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add this address as parameter
                mstore(0x04, address())
                // call to token
                pop(staticcall(gas(), underlying, 0x0, 0x24, 0x0, 0x20))
                // load the retrieved balance
                amount := mload(0x0)
            }

            let ptr := mload(0x40)

            // store common param
            mstore(add(ptr, 0x24), receiver)

            let cType := and(UINT8_MASK, shr(120, amountData))

            switch cType
            // 1 is the default non-protected collateral
            case 1 {
                // selector supply(uint256,address)
                mstore(ptr, DEPOSIT)
                mstore(add(ptr, 0x4), amount)
                // common param here
                // call silo
                if iszero(call(gas(), silo, 0x0, ptr, 0x44, 0x0, 0x0)) {
                    returndatacopy(0x0, 0x0, returndatasize())
                    revert(0x0, returndatasize())
                }
            }
            // others are id'ed by their enum
            default {
                // selector supply(uint256,address,uint256)
                mstore(ptr, DEPOSIT_WITH_COLLATERAL_TYPE)
                mstore(add(ptr, 0x4), amount)
                // common param here
                mstore(add(ptr, 0x44), cType)
                // call silo
                if iszero(call(gas(), silo, 0x0, ptr, 0x64, 0x0, 0x0)) {
                    returndatacopy(0x0, 0x0, returndatasize())
                    revert(0x0, returndatasize())
                }
            }
        }
        return currentOffset;
    }

    bytes32 private constant MAX_REPAY = 0x5f30114900000000000000000000000000000000000000000000000000000000;
    bytes32 private constant REPAY = 0xacb7081500000000000000000000000000000000000000000000000000000000;
    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | underlying                      |
     * | 20     | 16             | amount                          |
     * | 36     | 20             | receiver                        |
     * | 56     | 20             | silo                            |
     */

    function _repayToSiloV2(uint256 currentOffset) internal returns (uint256) {
        assembly {
            function _balanceOf(t, u) -> b {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add this address as parameter (u)
                mstore(0x04, u)
                // call to token
                pop(staticcall(gas(), t, 0x0, 0x24, 0x0, 0x20))
                // load the balance and return it
                b := mload(0x0)
            }

            let underlying := shr(96, calldataload(currentOffset))
            // offset for amount at lower bytes
            let amount := and(UINT120_MASK, shr(128, calldataload(add(currentOffset, 20))))
            // receiver
            let receiver := shr(96, calldataload(add(currentOffset, 36)))
            // get silo
            let silo := shr(96, calldataload(add(currentOffset, 56)))

            // skip silo (end of data)
            currentOffset := add(currentOffset, 76)

            switch amount
            case 0 { amount := _balanceOf(underlying, address()) }
            // safe repay maximum: fetch contract balance and user debt and take minimum
            case 0xffffffffffffffffffffffffffff {
                amount := _balanceOf(underlying, address())

                // call maxRepay(address) to get maxrepayable assets
                mstore(0, MAX_REPAY)
                // add caller address as parameter
                mstore(0x04, receiver)
                // call to debt token
                pop(staticcall(gas(), silo, 0x0, 0x24, 0x0, 0x20))
                // load the retrieved balance
                let borrowBalance := mload(0x0)
                // if borrow balance is less than the amount, select borrow balance
                if lt(borrowBalance, amount) { amount := borrowBalance }
            }

            let ptr := mload(0x40)

            // selector repay(uint256,address)
            mstore(ptr, REPAY)
            mstore(add(ptr, 0x04), amount)
            mstore(add(ptr, 0x24), receiver)
            // call silo
            if iszero(call(gas(), silo, 0x0, ptr, 0x44, 0x0, 0x0)) {
                returndatacopy(0x0, 0x0, returndatasize())
                revert(0x0, returndatasize())
            }
        }

        return currentOffset;
    }
}
