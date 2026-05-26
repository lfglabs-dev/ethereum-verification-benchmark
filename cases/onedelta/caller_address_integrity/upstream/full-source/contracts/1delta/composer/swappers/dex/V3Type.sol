// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title Uniswap V3 type swapper contract
 * @notice Executes Cl swaps and pushes data to the callbacks
 * the data can be empty, the callback then jsut fills the swap
 */
abstract contract V3TypeGeneric is Masks {
    constructor() {}

    /*
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 1              | forkId               |
     * | 21     | 2              | fee                  |
     * | 23     | 2              | calldataLength       |
     * | 25     | calldataLength | calldata             |
     */
    function _swapUniswapV3PoolExactInGeneric(
        uint256 fromAmount,
        address tokenIn,
        address tokenOut,
        address receiver,
        uint256 currentOffset,
        address callerAddress
    )
        internal
        returns (uint256 receivedAmount, uint256)
    {
        // solhint-disable-next-line no-inline-assembly
        assembly {
            let ptr := mload(0x40)
            // read the pool address
            let pool := calldataload(currentOffset)
            // skip pool
            currentOffset := add(currentOffset, 20)
            let clLength := and(UINT16_MASK, shr(56, pool))
            pool :=
                shr(
                    96,
                    pool // starts as first param
                )
            let zeroForOne :=
                lt(
                    tokenIn,
                    tokenOut //
                )
            // Prepare external call data
            // Store swap selector (0x128acb08)
            mstore(ptr, 0x128acb0800000000000000000000000000000000000000000000000000000000)
            // Store toAddress
            mstore(add(ptr, 4), receiver)
            // Store direction
            mstore(add(ptr, 36), zeroForOne)
            // Store fromAmount
            mstore(add(ptr, 68), fromAmount)

            // Store data offset
            mstore(add(ptr, 132), 0xa0)
            let plStored := add(clLength, 65)
            // Store data length
            mstore(add(ptr, 164), plStored)

            /*
             * Store the data for the callback as follows
             * | Offset | Length (bytes) | Description          |
             * |--------|----------------|----------------------|
             * | 0      | 20             | caller               |
             * | 20     | 20             | tokenIn              |
             * | 40     | 20             | tokenOut             |
             * | 60     | 1              | dexId                | <- we use calldatacopy from here
             * | 61     | 2              | fee                  |
             * | 63     | 2              | calldataLength       |
             * | 65     | calldataLength | calldata             |
             */
            mstore(add(ptr, 196), shl(96, callerAddress))
            mstore(add(ptr, 216), shl(96, tokenIn))
            mstore(add(ptr, 236), shl(96, tokenOut))
            // Store furhter calldata (add 4 to length due to fee and clLength)
            calldatacopy(add(ptr, 256), currentOffset, add(clLength, 5))

            switch zeroForOne
            case 0 {
                // Store sqrtPriceLimitX96
                mstore(add(ptr, 100), MAX_SQRT_RATIO)

                // Perform the external 'swap' call
                if iszero(call(gas(), pool, 0, ptr, add(228, plStored), ptr, 32)) {
                    // store return value directly to free memory pointer
                    // The call failed; we retrieve the exact error message and revert with it
                    returndatacopy(0, 0, returndatasize()) // Copy the error message to the start of memory
                    revert(0, returndatasize()) // Revert with the error message
                }
                // If direction is 0, return amount0
                receivedAmount := mload(ptr)
            }
            default {
                // Store sqrtPriceLimitX96
                mstore(add(ptr, 100), MIN_SQRT_RATIO)

                // Perform the external 'swap' call
                if iszero(call(gas(), pool, 0, ptr, add(228, plStored), ptr, 64)) {
                    // store return value directly to free memory pointer
                    // The call failed; we retrieve the exact error message and revert with it
                    returndatacopy(0, 0, returndatasize()) // Copy the error message to the start of memory
                    revert(0, returndatasize()) // Revert with the error message
                }

                // If direction is 1, return amount1
                receivedAmount := mload(add(ptr, 32))
            }
            // receivedAmount = -receivedAmount
            receivedAmount := sub(0, receivedAmount)

            switch lt(clLength, 2)
            case 1 { currentOffset := add(currentOffset, 5) }
            default { currentOffset := add(currentOffset, add(5, clLength)) }
        }
        return (receivedAmount, currentOffset);
    }

    /// @dev Swap exact input through izumi
    function _swapIZIPoolExactInGeneric(
        uint256 fromAmount,
        address tokenIn,
        address tokenOut,
        address receiver,
        uint256 currentOffset,
        address callerAddress
    )
        internal
        returns (uint256 receivedAmount, uint256)
    {
        // solhint-disable-next-line no-inline-assembly
        assembly {
            let ptr := mload(0x40)
            // read the pool address
            let pool := calldataload(currentOffset)
            // skip pool
            currentOffset := add(currentOffset, 20)
            let clLength := and(UINT16_MASK, shr(56, pool))
            pool :=
                shr(
                    96,
                    pool // starts as first param
                )
            switch lt(
                tokenIn,
                tokenOut //
            )
            case 0 {
                // Prepare external call data
                // Store swapY2X selector (0x2c481252)
                mstore(ptr, 0x2c48125200000000000000000000000000000000000000000000000000000000)
                // Store recipient
                mstore(add(ptr, 4), receiver)
                // Store fromAmount
                mstore(add(ptr, 36), fromAmount)
                // Store highPt
                mstore(add(ptr, 68), 799999)
                // Store data offset
                mstore(add(ptr, 100), 0x80)

                let plStored := add(clLength, 65)
                // Store data length
                mstore(add(ptr, 132), plStored)

                /*
                 * Store the data for the callback as follows
                 * | Offset | Length (bytes) | Description          |
                 * |--------|----------------|----------------------|
                 * | 0      | 20             | caller               |
                 * | 20     | 20             | tokenIn              |
                 * | 40     | 20             | tokenOut             |
                 * | 60     | 1              | dexId                |
                 * | 61     | 2              | fee                  | <- we use calldatacopy from here
                 * | 63     | 2              | calldataLength       |
                 * | 65     | calldataLength | calldata             |
                 */
                mstore(add(ptr, 164), shl(96, callerAddress))
                mstore(add(ptr, 184), shl(96, tokenIn))
                mstore(add(ptr, 204), shl(96, tokenOut))

                // Store furhter calldata
                calldatacopy(add(ptr, 224), currentOffset, add(clLength, 5))

                // Perform the external 'swap' call
                if iszero(call(gas(), pool, 0, ptr, add(196, plStored), ptr, 32)) {
                    // store return value directly to free memory pointer
                    // The call failed; we retrieve the exact error message and revert with it
                    returndatacopy(0, 0, returndatasize()) // Copy the error message to the start of memory
                    revert(0, returndatasize()) // Revert with the error message
                }
                // If direction is 0, return amount0
                receivedAmount := mload(ptr)
            }
            default {
                // Prepare external call data
                // Store swapX2Y selector (0x857f812f)
                mstore(ptr, 0x857f812f00000000000000000000000000000000000000000000000000000000)
                // Store toAddress
                mstore(add(ptr, 4), receiver)
                // Store fromAmount
                mstore(add(ptr, 36), fromAmount)
                // Store sqrtPriceLimitX96
                mstore(add(ptr, 68), sub(0, 799999))
                // Store data offset
                mstore(add(ptr, 100), 0x80)

                let plStored := add(clLength, 65)
                // Store data length
                mstore(add(ptr, 132), plStored)

                /*
                 * Store the data for the callback as follows
                 * | Offset | Length (bytes) | Description          |
                 * |--------|----------------|----------------------|
                 * | 0      | 20             | caller               |
                 * | 20     | 20             | tokenIn              |
                 * | 40     | 20             | tokenOut             |
                 * | 60     | 1              | dexId                |
                 * | 61     | 2              | fee                  | <- we use calldatacopy from here
                 * | 63     | 2              | calldataLength       |
                 * | 65     | calldataLength | calldata             |
                 */
                mstore(add(ptr, 164), shl(96, callerAddress))
                mstore(add(ptr, 184), shl(96, tokenIn))
                mstore(add(ptr, 204), shl(96, tokenOut))

                // Store furhter calldata
                calldatacopy(add(ptr, 224), currentOffset, add(clLength, 5))

                // Perform the external 'swap' call
                if iszero(call(gas(), pool, 0, ptr, add(196, plStored), ptr, 64)) {
                    // store return value directly to free memory pointer
                    // The call failed; we retrieve the exact error message and revert with it
                    returndatacopy(0, 0, returndatasize()) // Copy the error message to the start of memory
                    revert(0, returndatasize()) // Revert with the error message
                }
                // If direction is 1, return amount1
                receivedAmount := mload(add(ptr, 32))
            }

            switch lt(clLength, 2)
            case 1 { currentOffset := add(currentOffset, 5) }
            default { currentOffset := add(currentOffset, add(5, clLength)) }
        }
        return (receivedAmount, currentOffset);
    }
}
