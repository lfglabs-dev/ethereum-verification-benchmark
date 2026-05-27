// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {BaseUtils} from "contracts/1delta/composer/generic/BaseUtils.sol";

// solhint-disable max-line-length

/**
 * @notice External call on call forwarder which can safely execute any calls for a specific selector
 * without comprimising this contract
 */
abstract contract ExternalCall is BaseUtils {
    /// @notice selector for deltaForwardCompose(bytes)
    bytes32 private constant DELTA_FORWARD_COMPOSE = 0x6a0c90ff00000000000000000000000000000000000000000000000000000000;

    /**
     * This is not a real external call, this one has a pre-determined selector
     * that prevents collision with any calls that can be made in this contract
     * This prevents unauthorized calls that would pull funds from other users
     *
     * On top of that, this makes the contract arbitrarily extensible.
     */
    function _callExternal(uint256 currentOffset) internal returns (uint256) {
        /*
         * | Offset | Length (bytes) | Description          |
         * |--------|----------------|----------------------|
         * | 0      | 20             | target               |
         * | 20     | 16             | nativeValue          |
         * | 36     | 2              | calldataLength       |
         * | 38     | calldataLength | calldata             |
         */
        assembly {
            let target := shr(96, calldataload(currentOffset))
            currentOffset := add(20, currentOffset)

            let callValue := shr(128, calldataload(currentOffset))
            currentOffset := add(16, currentOffset)

            let dataLength := shr(240, calldataload(currentOffset))
            currentOffset := add(2, currentOffset)

            // this is a slightly different behavior as, unlike for ERC20, the
            // 0-value is a commonly used one, as such, a flag is used for this
            switch and(NATIVE_FLAG, callValue)
            case 0 { callValue := and(callValue, UINT120_MASK) }
            default { callValue := selfbalance() }

            // free memo ptr for populating the tx
            let ptr := mload(0x40)

            mstore(ptr, DELTA_FORWARD_COMPOSE)
            mstore(add(ptr, 0x4), 0x20) // offset
            mstore(add(ptr, 0x24), dataLength) // length

            // copy calldata
            calldatacopy(add(ptr, 0x44), currentOffset, dataLength)
            if iszero(
                call(
                    gas(),
                    target,
                    callValue,
                    ptr, //
                    add(0x44, dataLength),
                    //selector plus 0x44 (selector, offset, length)
                    0x0, // output = empty
                    0x0 // output size = zero
                )
            ) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
            // increment offset by data length
            currentOffset := add(currentOffset, dataLength)
        }
        return currentOffset;
    }
}
