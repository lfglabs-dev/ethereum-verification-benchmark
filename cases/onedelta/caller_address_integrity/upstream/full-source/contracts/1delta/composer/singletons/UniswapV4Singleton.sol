// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {Masks} from "../../shared/masks/Masks.sol";
import {DeltaErrors} from "../../shared/errors/Errors.sol";
import {Gen2025ActionIds} from "../enums/DeltaEnums.sol";

// solhint-disable max-line-length

/**
 * @notice Everything Uniswap V4 & Balancer V3, the major upgrades for DEXs in 2025
 */
abstract contract UniswapV4SingletonActions is Masks, DeltaErrors {
    // Uni V4 selectors needed for executing a flash loan
    bytes32 private constant TAKE = 0x0b0d9c0900000000000000000000000000000000000000000000000000000000;
    bytes32 private constant SETTLE = 0x11da60b400000000000000000000000000000000000000000000000000000000;
    bytes32 private constant SYNC = 0xa584119400000000000000000000000000000000000000000000000000000000;

    function _unoV4Take(uint256 currentOffset) internal returns (uint256) {
        /*
         * | Offset | Length (bytes) | Description         |
         * |--------|----------------|---------------------|
         * | 0      | 20             | manager             |
         * | 20     | 20             | asset               |
         * | 40     | 20             | receiver            |
         * | 60     | 16             | amount              |
         */
        assembly {
            let manager := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)
            let asset := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)
            let receiver := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)
            let amount := shr(128, calldataload(currentOffset))

            // free memo ptr for populating the tx
            let ptr := mload(0x40)

            mstore(ptr, TAKE)
            mstore(add(ptr, 4), asset) // offset
            mstore(add(ptr, 36), receiver)
            mstore(add(ptr, 68), amount)

            if iszero(
                call(
                    gas(),
                    manager,
                    0x0,
                    ptr, //
                    100,
                    // selector, offset, length, data
                    0x0, // output = empty
                    0x0 // output size = zero
                )
            ) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
            // increment offset by amount length
            currentOffset := add(currentOffset, 16)
        }
        return currentOffset;
    }

    function _unoV4Sync(uint256 currentOffset) internal returns (uint256) {
        /*
         * | Offset | Length (bytes) | Description   |
         * |--------|----------------|---------------|
         * | 0      | 20             | manager       |
         * | 20     | 20             | asset         |
         */
        assembly {
            let manager := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)
            let asset := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)

            mstore(0, SYNC)
            mstore(4, asset) // offset

            if iszero(
                call(
                    gas(),
                    manager,
                    0x0,
                    0, //
                    36,
                    // selector, offset, length, data
                    0x0, // output = empty
                    0x0 // output size = zero
                )
            ) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
        }
        return currentOffset;
    }

    function _unoV4Settle(uint256 currentOffset) internal returns (uint256) {
        /*
         * | Offset | Length (bytes) | Description       |
         * |--------|----------------|-------------------|
         * | 0      | 20             | manager           |
         * | 20     | 16             | nativeAmount      |
         */
        assembly {
            let manager := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)
            let amount := shr(128, calldataload(currentOffset))

            currentOffset := add(16, currentOffset)

            mstore(0, SETTLE)
            if iszero(
                call(
                    gas(),
                    manager,
                    amount,
                    0, //
                    4,
                    // selector, offset, length, data
                    0x0, // output = empty
                    0x0 // output size = zero
                )
            ) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
        }
        return currentOffset;
    }
}
