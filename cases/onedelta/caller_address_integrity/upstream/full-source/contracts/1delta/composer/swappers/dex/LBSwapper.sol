// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title LB swapper contract
 */
abstract contract LBSwapper is ERC20Selectors, Masks {
    /**
     * Swaps exact input on LB
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 1              | swapForY             |
     * | 21     | 1              | pay flag             | <- 0: caller pays; 1: contract pays; greater: pre-funded
     */
    function _swapLBexactIn(
        uint256 fromAmount,
        address tokenIn,
        address receiver,
        address callerAddress,
        uint256 currentOffset //
    )
        internal
        returns (uint256 amountOut, uint256 payFlag)
    {
        assembly {
            let ptr := mload(0x40)
            let lbData := calldataload(currentOffset)
            let pool := shr(96, lbData)

            // pre-funded is >= 2
            payFlag := and(UINT8_MASK, shr(80, lbData))
            if lt(payFlag, 2) {
                let success
                // payFlag evaluation
                switch payFlag
                case 0 {
                    // selector for transferFrom(address,address,uint256)
                    mstore(ptr, ERC20_TRANSFER_FROM)
                    mstore(add(ptr, 0x04), callerAddress)
                    mstore(add(ptr, 0x24), pool)
                    mstore(add(ptr, 0x44), fromAmount)
                    success := call(gas(), tokenIn, 0, ptr, 0x64, 0, 32)
                }
                // transfer plain
                case 1 {
                    // selector for transfer(address,uint256)
                    mstore(ptr, ERC20_TRANSFER)
                    mstore(add(ptr, 0x04), pool)
                    mstore(add(ptr, 0x24), fromAmount)
                    success := call(gas(), tokenIn, 0, ptr, 0x44, 0, 32)
                }

                let rdsize := returndatasize()

                // revert if needed
                if iszero(
                    and(
                        success, // call itself succeeded
                        or(
                            iszero(rdsize), // no return data, or
                            and(
                                gt(rdsize, 31), // at least 32 bytes
                                eq(mload(0), 1) // starts with uint256(1)
                            )
                        )
                    )
                ) {
                    returndatacopy(0, 0, rdsize)
                    revert(0, rdsize)
                }
            }

            // swap for Y flag
            let swapForY := and(UINT8_MASK, shr(88, lbData))
            ////////////////////////////////////////////////////
            // Execute swap function
            ////////////////////////////////////////////////////

            // swap(bool,address)
            mstore(ptr, 0x53c059a000000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 0x4), swapForY)
            mstore(add(ptr, 0x24), receiver)
            // call swap, revert if invalid/undefined pool
            if iszero(call(gas(), pool, 0x0, ptr, 0x44, ptr, 0x20)) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
            // the swap call returns both amounts encoded into a single bytes32 as (amountX,amountY)
            switch swapForY
            case 0 { amountOut := and(mload(ptr), UINT128_MASK) }
            default { amountOut := shr(128, mload(ptr)) }
            // skip 22 bytes
            currentOffset := add(currentOffset, 22)
        }
        return (amountOut, currentOffset);
    }
}
