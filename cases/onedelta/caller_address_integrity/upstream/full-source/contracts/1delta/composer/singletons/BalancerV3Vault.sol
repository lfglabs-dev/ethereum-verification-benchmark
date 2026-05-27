// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {Masks} from "../../shared/masks/Masks.sol";
import {DeltaErrors} from "../../shared/errors/Errors.sol";
import {Gen2025ActionIds} from "../enums/DeltaEnums.sol";

// solhint-disable max-line-length

/**
 * @notice Balancer V3 actions
 */
abstract contract BalancerV3VaultActions is Masks, DeltaErrors {
    // Balancer V3 selectors needed for executing a flash loan
    /// @notice UniV4 pendant: take()
    bytes32 private constant SEND_TO = 0xae63932900000000000000000000000000000000000000000000000000000000;
    /// @notice same selector string name as for UniV4, different params for balancer
    bytes32 private constant SETTLE = 0x15afd40900000000000000000000000000000000000000000000000000000000;

    constructor() {}

    function _encodeBalancerV3Take(uint256 currentOffset) internal returns (uint256) {
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

            mstore(ptr, SEND_TO)
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

    function _balancerV3Settle(uint256 currentOffset) internal returns (uint256) {
        /*
         * | Offset | Length (bytes) | Description       |
         * |--------|----------------|-------------------|
         * | 0      | 20             | manager           |
         * | 20     | 20             | asset             | <-- never native
         * | 40     | 16             | amountHint        |
         */
        assembly {
            let manager := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)
            let asset := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)
            let amountHint := shr(128, calldataload(currentOffset))

            // we can settle exactly for the credit as for the B3 logic
            if eq(amountHint, UINT128_MASK) { amountHint := MAX_UINT256 }

            currentOffset := add(16, currentOffset)

            let ptr := mload(0x40)
            // settle amount
            mstore(ptr, SETTLE)
            mstore(add(ptr, 4), asset)
            mstore(add(ptr, 36), amountHint)
            if iszero(
                call(
                    gas(),
                    manager,
                    0x0, // no native
                    ptr, //
                    68,
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
