// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {ERC20Selectors} from "../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../shared/masks/Masks.sol";

// solhint-disable max-line-length

/**
 * @notice Lending base contract that wraps Cmpound V3 markets
 */
abstract contract CompoundV3Lending is ERC20Selectors, Masks {
    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | underlying                      |
     * | 20     | 16             | amount                          |
     * | 36     | 20             | receiver                        |
     * | 76     | 1              | isBase                          |
     * | 77     | 20             | pool                            |
     */
    function _withdrawFromCompoundV3(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            let ptr := mload(0x40)
            // Compound V3 types need to trasfer collateral tokens

            let underlying := shr(96, calldataload(currentOffset))
            // offset for amount at lower bytes
            let amountData := shr(128, calldataload(add(currentOffset, 20)))

            let isBase := calldataload(add(currentOffset, 36))
            // receiver
            let receiver := shr(96, isBase)

            // adjust isBase flag

            let cometPool := shr(96, calldataload(add(currentOffset, 57)))

            currentOffset := add(currentOffset, 77)

            let amount := and(UINT120_MASK, amountData)
            if eq(amount, 0xffffffffffffffffffffffffffff) {
                switch and(UINT8_MASK, shr(88, isBase))
                case 0 {
                    // selector for userCollateral(address,address)
                    mstore(ptr, 0x2b92a07d00000000000000000000000000000000000000000000000000000000)
                    // add caller address as parameter
                    mstore(add(ptr, 0x04), callerAddress)
                    // add underlying address
                    mstore(add(ptr, 0x24), underlying)
                    // call to comet
                    pop(staticcall(gas(), cometPool, ptr, 0x44, ptr, 0x20))
                    // load the retrieved balance (lower 128 bits)
                    amount := and(UINT128_MASK, mload(ptr))
                }
                // comet.balanceOf(...) is lending token balance
                default {
                    // selector for balanceOf(address)
                    mstore(0, ERC20_BALANCE_OF)
                    // add caller address as parameter
                    mstore(0x04, callerAddress)
                    // call to comet
                    pop(staticcall(gas(), cometPool, 0x0, 0x24, 0x0, 0x20))
                    // load the retrieved balance
                    amount := mload(0x0)
                }
            }

            // selector withdrawFrom(address,address,address,uint256)
            mstore(ptr, 0x2644131800000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 0x04), callerAddress)
            mstore(add(ptr, 0x24), receiver)
            mstore(add(ptr, 0x44), underlying)
            mstore(add(ptr, 0x64), amount)
            // call pool
            if iszero(call(gas(), cometPool, 0x0, ptr, 0x84, 0x0, 0x0)) {
                returndatacopy(0x0, 0x0, returndatasize())
                revert(0x0, returndatasize())
            }
        }
        return currentOffset;
    }

    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | underlying                      |
     * | 20     | 16             | amount                          |
     * | 36     | 20             | receiver                        |
     * | 76     | 20             | comet                           |
     */
    function _borrowFromCompoundV3(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            let ptr := mload(0x40)
            // Compound V3 types need to trasfer collateral tokens
            let underlying := shr(96, calldataload(currentOffset))
            // offset for amount at lower bytes
            let amountData := shr(128, calldataload(add(currentOffset, 20)))
            // receiver
            let receiver := shr(96, calldataload(add(currentOffset, 36)))

            let cometPool := shr(96, calldataload(add(currentOffset, 56)))

            currentOffset := add(currentOffset, 76)

            let amount := and(UINT120_MASK, amountData)

            // selector withdrawFrom(address,address,address,uint256)
            mstore(ptr, 0x2644131800000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 0x04), callerAddress)
            mstore(add(ptr, 0x24), receiver)
            mstore(add(ptr, 0x44), underlying)
            mstore(add(ptr, 0x64), amount)
            // call pool
            if iszero(call(gas(), cometPool, 0x0, ptr, 0x84, 0x0, 0x0)) {
                returndatacopy(0x0, 0x0, returndatasize())
                revert(0x0, returndatasize())
            }
        }
        return currentOffset;
    }

    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | underlying                      |
     * | 20     | 16             | amount                          |
     * | 36     | 20             | receiver                        |
     * | 76     | 20             | comet                           |
     */
    /// @notice Withdraw from lender lastgiven user address and lender Id
    function _depositToCompoundV3(uint256 currentOffset) internal returns (uint256) {
        assembly {
            let underlying := shr(96, calldataload(currentOffset))
            // offset for amount at lower bytes
            let amountData := shr(128, calldataload(add(currentOffset, 20)))
            // receiver
            let receiver := shr(96, calldataload(add(currentOffset, 36)))
            // get comet
            let comet := shr(96, calldataload(add(currentOffset, 56)))
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

            // selector supplyTo(address,address,uint256)
            mstore(ptr, 0x4232cd6300000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 0x04), receiver)
            mstore(add(ptr, 0x24), underlying)
            mstore(add(ptr, 0x44), amount)
            // call pool
            if iszero(call(gas(), comet, 0x0, ptr, 0x64, 0x0, 0x0)) {
                returndatacopy(0x0, 0x0, returndatasize())
                revert(0x0, returndatasize())
            }
        }
        return currentOffset;
    }

    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | underlying                      |
     * | 20     | 16             | amount                          |
     * | 36     | 20             | receiver                        |
     * | 76     | 20             | comet                           |
     */
    function _repayToCompoundV3(uint256 currentOffset) internal returns (uint256) {
        assembly {
            let underlying := shr(96, calldataload(currentOffset))
            // offset for amount at lower bytes
            let amountData := shr(128, calldataload(add(currentOffset, 20)))
            // receiver
            let receiver := shr(96, calldataload(add(currentOffset, 36)))
            // get comet
            let comet := shr(96, calldataload(add(currentOffset, 56)))
            currentOffset := add(currentOffset, 76)

            let amount := and(UINT120_MASK, amountData)
            switch amount
            case 0 {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add this address as parameter
                mstore(0x04, address())
                // call to token
                pop(staticcall(gas(), underlying, 0x0, 0x24, 0x0, 0x20))
                // load the retrieved balance
                amount := mload(0x0)
            }
            // repay maximum safely
            // comet will fail when using blind maxima if the contract has not
            // enough balance
            // to prevent this, we read the contract balance and user borrow balance and take the minimum
            case 0xffffffffffffffffffffffffffff {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add this address as parameter
                mstore(0x04, address())
                // call to token
                pop(staticcall(gas(), underlying, 0x0, 0x24, 0x0, 0x20))
                // load the retrieved balance
                amount := mload(0x0)

                // selector for borrowBalanceOf(address)
                mstore(0, 0x374c49b400000000000000000000000000000000000000000000000000000000)
                // add receiver as parameter
                mstore(0x04, receiver)
                // call to comet
                pop(staticcall(gas(), comet, 0x0, 0x24, 0x0, 0x20))
                let userBorrowBalance := mload(0x0)

                // amount greater than borrow balance -> use borrow balance
                // otherwise repay less than the borrow balance safely
                if gt(amount, userBorrowBalance) { amount := userBorrowBalance }
            }

            let ptr := mload(0x40)
            // selector supplyTo(address,address,uint256)
            mstore(ptr, 0x4232cd6300000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 0x04), receiver)
            mstore(add(ptr, 0x24), underlying)
            mstore(add(ptr, 0x44), amount)
            // call pool
            if iszero(call(gas(), comet, 0x0, ptr, 0x64, 0x0, 0x0)) {
                returndatacopy(0x0, 0x0, returndatasize())
                revert(0x0, returndatasize())
            }
        }

        return currentOffset;
    }
}
