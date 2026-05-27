// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {Slots} from "../../../slots/Slots.sol";
import {Masks} from "../../../../shared/masks/Masks.sol";

/**
 * Flash loaning through BalancerV2
 */
abstract contract BalancerV2FlashLoans is Slots, Masks {
    address private constant BALANCER_V2 = 0xBA12222222228d8Ba445958a75a0704d566BF2C8;
    address private constant SWAAP = 0xd315a9C38eC871068FEC378E4Ce78AF528C76293;

    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | asset                           |
     * | 20     | 16             | amount                          |
     * | 36     | 2              | paramsLength                    |
     * | 38     | paramsLength   | params                          | <- the first param here is the poolId 
     */
    function balancerV2FlashLoan(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            // get token to loan
            let token := shr(96, calldataload(currentOffset))

            // second calldata slice including amount annd params length
            let slice := calldataload(add(currentOffset, 20))
            let amount := shr(128, slice) // shr will already mask uint112 here
            // length of params
            let calldataLength := and(UINT16_MASK, shr(112, slice))

            let pool
            // switch-case over poolId to ensure trusted target
            switch and(UINT8_MASK, shr(104, slice))
            case 0 { pool := BALANCER_V2 }
            case 2 { pool := SWAAP }
            default { revert(0, 0) }
            // skip addresses and amount
            currentOffset := add(currentOffset, 38)
            // balancer should be the secondary choice
            let ptr := mload(0x40)
            // flashLoan(...)
            mstore(ptr, 0x5c38449e00000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 4), address()) // receiver
            mstore(add(ptr, 36), 0x80) // offset assets
            mstore(add(ptr, 68), 0xc0) // offset amounts
            mstore(add(ptr, 100), 0x100) // offset calldata
            mstore(add(ptr, 132), 1) // length assets
            mstore(add(ptr, 164), token) // asset
            mstore(add(ptr, 196), 1) // length amounts
            mstore(add(ptr, 228), amount) // amount
            mstore(add(ptr, 260), add(20, calldataLength)) // length calldata
            // caller at the beginning
            mstore(add(ptr, 292), shl(96, callerAddress))
            calldatacopy(add(ptr, 312), currentOffset, calldataLength) // calldata
            // set entry flag
            tstore(FLASH_LOAN_GATEWAY_SLOT, 1)
            if iszero(
                call(
                    gas(),
                    pool,
                    0x0,
                    ptr,
                    add(calldataLength, 312), // = 10 * 32 + 4
                    0x0,
                    0x0 //
                )
            ) {
                let rdlen := returndatasize()
                returndatacopy(0, 0, rdlen)
                revert(0x0, rdlen)
            }
            // we require that the callbacks implement unsetting the entry flag after validating them
            // otherwise, one could use 2 valid balancer clones, open the gateway with the first and
            // then reenter with the second one, passing the gateway check
            // increment offset
            currentOffset := add(currentOffset, calldataLength)
        }
        return currentOffset;
    }
}
