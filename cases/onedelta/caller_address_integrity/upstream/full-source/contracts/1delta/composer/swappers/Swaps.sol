// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {BaseSwapper} from "./BaseSwapper.sol";

// solhint-disable max-line-length

/**
 * @notice entrypoint for swaps
 * - supports a broad variety of DEXs
 * - this also is the entrypoint for flash-swaps, one only needs to
 *   add calldata to the respective call to trigger it
 */
abstract contract Swaps is BaseSwapper {
    function _swap(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        uint256 amountIn;
        uint256 minimumAmountReceived;
        address tokenIn;
        /*
         * Store the data for the callback as follows
         * | Offset | Length (bytes) | Description          |
         * |--------|----------------|----------------------|
         * | 0      | 16             | amount               | <-- input amount
         * | 16     | 16             | amountMax            | <-- slippage check
         * | 32     | 20             | tokenIn              |
         * | 52     | any            | data                 |
         *
         * `data` is a path matrix definition (see BaseSwapepr)
         */
        assembly {
            minimumAmountReceived := calldataload(currentOffset)
            amountIn := shr(128, minimumAmountReceived)
            minimumAmountReceived := and(UINT128_MASK, minimumAmountReceived)
            currentOffset := add(currentOffset, 32)
            let dataStart := calldataload(currentOffset)
            tokenIn := shr(96, dataStart)
            currentOffset := add(20, currentOffset)

            /**
             * if the amount is zero, we assume that the contract balance is swapped
             */
            if iszero(amountIn) {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add this address as parameter
                mstore(0x04, address())
                // call to token
                pop(staticcall(gas(), tokenIn, 0x0, 0x24, 0x0, 0x20))
                // load the retrieved balance
                amountIn := mload(0x0)
            }
        }
        (amountIn, currentOffset,) = _singleSwapSplitOrRoute(
            amountIn,
            tokenIn,
            callerAddress,
            currentOffset //
        );

        assembly {
            if gt(minimumAmountReceived, amountIn) {
                mstore(0x0, SLIPPAGE)
                revert(0x0, 0x4)
            }
        }
        return currentOffset;
    }
}
