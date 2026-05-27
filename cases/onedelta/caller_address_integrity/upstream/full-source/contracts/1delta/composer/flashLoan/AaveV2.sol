// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {Masks} from "../../shared/masks/Masks.sol";

/**
 * @title Aave V2 flash loan executor
 * @author 1delta Labs AG
 */
contract AaveV2FlashLoans is Masks {
    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | asset                           |
     * | 20     | 20             | pool                            | <-- we allow ANY aave v2 style pool here
     * | 40     | 16             | amount                          |
     * | 56     | 2              | paramsLength                    |
     * | 58     | paramsLength   | params                          |
     */
    function aaveV2FlashLoan(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            // get token to loan
            let token := shr(96, calldataload(currentOffset))

            // target to call
            let pool := shr(96, calldataload(add(currentOffset, 20)))

            // second calldata slice including amount annd params length
            let slice := calldataload(add(currentOffset, 40))
            let amount := shr(128, slice) // shr will already mask uint112 here
            // length of params
            let calldataLength := and(UINT16_MASK, shr(112, slice))

            // skip addresses and amount
            currentOffset := add(currentOffset, 58)

            // call flash loan
            let ptr := mload(0x40)
            // flashLoan(...) (See Aave V2 ILendingPool)
            mstore(ptr, 0xab9c4b5d00000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 4), address()) // receiver is this address
            mstore(add(ptr, 36), 0x0e0) // offset assets
            mstore(add(ptr, 68), 0x120) // offset amounts
            mstore(add(ptr, 100), 0x160) // offset modes
            mstore(add(ptr, 132), 0) // onBefhalfOf = 0
            mstore(add(ptr, 164), 0x1a0) // offset calldata
            mstore(add(ptr, 196), 0) // referral code = 0
            mstore(add(ptr, 228), 1) // length assets
            mstore(add(ptr, 260), token) // assets[0]
            mstore(add(ptr, 292), 1) // length amounts
            mstore(add(ptr, 324), amount) // amounts[0]
            mstore(add(ptr, 356), 1) // length modes
            mstore(add(ptr, 388), 0) // mode = 0
            ////////////////////////////////////////////////////
            // We attach [caller] as first 20 bytes
            ////////////////////////////////////////////////////
            mstore(add(ptr, 420), add(20, calldataLength)) // length calldata (plus 1 + address)
            // caller at the beginning
            mstore(add(ptr, 452), shl(96, callerAddress))

            // copy the calldataslice for the params
            calldatacopy(
                add(ptr, 472), // next slot
                currentOffset, // offset starts at 27, already incremented
                calldataLength // copy given length
            ) // calldata
            if iszero(
                call(
                    gas(),
                    pool,
                    0x0,
                    ptr,
                    add(calldataLength, 472), // = 14 * 32 + 4 + 20 (caller)
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
