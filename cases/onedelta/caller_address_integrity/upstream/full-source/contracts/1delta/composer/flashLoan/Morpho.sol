// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {Masks} from "../../shared/masks/Masks.sol";

/**
 * @title Morpho flash loans
 * @author 1delta Labs AG
 */
contract MorphoFlashLoans is Masks {
    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | asset                           |
     * | 20     | 20             | pool                            | <-- we allow ANY morpho style pool here
     * | 40     | 16             | amount                          |
     * | 56     | 2              | paramsLength                    |
     * | 58     | paramsLength   | params                          |
     */
    function morphoFlashLoan(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            // get token to loan
            let token := shr(96, calldataload(currentOffset))
            // morpho-like pool as target
            let pool := shr(96, calldataload(add(currentOffset, 20)))
            // second calldata slice including amount annd params length
            let slice := calldataload(add(currentOffset, 40))
            let amount := shr(128, slice) // shr will already mask uint128 here
            // length of params
            let calldataLength := and(UINT16_MASK, shr(112, slice))
            // skip uint128 and uint16
            currentOffset := add(currentOffset, 58)

            // morpho should be the primary choice
            let ptr := mload(0x40)

            /**
             * Prepare call
             */

            // flashLoan(...)
            mstore(ptr, 0xe0232b4200000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 4), token)
            mstore(add(ptr, 36), amount)
            mstore(add(ptr, 68), 0x60) // offset
            mstore(add(ptr, 100), add(20, calldataLength)) // data length
            mstore(add(ptr, 132), shl(96, callerAddress)) // caller
            calldatacopy(add(ptr, 152), currentOffset, calldataLength) // calldata
            if iszero(
                call(
                    gas(),
                    pool,
                    0x0,
                    ptr,
                    add(calldataLength, 152),
                    0x0,
                    0x0 //
                )
            ) {
                returndatacopy(0, 0, returndatasize())
                revert(0x0, returndatasize())
            }
            // increment offset
            currentOffset := add(currentOffset, calldataLength)
        }
        return currentOffset;
    }
}
