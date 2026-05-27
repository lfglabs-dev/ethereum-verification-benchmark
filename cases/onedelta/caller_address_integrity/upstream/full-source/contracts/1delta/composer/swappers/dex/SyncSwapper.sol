// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title SyncSwap style swapper, pre-funded, all pool variations
 */
abstract contract SyncSwapper is ERC20Selectors, Masks {
    /// @dev selector for swap(bytes,address,address,bytes)
    bytes32 internal constant SYNCSWAP_SELECTOR = 0x7132bb7f00000000000000000000000000000000000000000000000000000000;

    /**
     * Swaps exact input on SyncSwap
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 1              | pay flag             | <- 0: caller pays; 1: contract pays; greater: pre-funded
     */
    function _swapSyncExactIn(
        uint256 fromAmount,
        address tokenIn,
        address receiver,
        address callerAddress,
        uint256 currentOffset //
    )
        internal
        returns (uint256 buyAmount, uint256 payFlag)
    {
        assembly {
            let syncSwapData := calldataload(currentOffset)

            let ptr := mload(0x40)

            // facilitate payment if needed
            payFlag := and(UINT8_MASK, shr(88, syncSwapData))
            let pool := shr(96, syncSwapData)
            if lt(payFlag, 2) {
                let success
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
                // Check for ERC20 success. ERC20 tokens should return a boolean,
                // but some don't. We accept 0-length return data as success, or at
                // least 32 bytes that starts with a 32-byte boolean true.
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

            // selector for swap(...)
            mstore(ptr, SYNCSWAP_SELECTOR)
            mstore(add(ptr, 4), 0x80) // first param set offset
            mstore(add(ptr, 36), 0x0) // sender address
            ////////////////////////////////////////////////////
            // We store the bytes length to zero (no callback)
            // and directly trigger the swap
            ////////////////////////////////////////////////////
            mstore(add(ptr, 68), 0x0) // callback receiver address
            mstore(add(ptr, 100), 0x100) // calldata offset
            mstore(add(ptr, 132), 0x60) // datalength
            mstore(add(ptr, 164), tokenIn) // tokenIn
            mstore(add(ptr, 196), receiver) // to
            mstore(add(ptr, 228), 0) // withdraw mode
            mstore(add(ptr, 260), 0) // path length is zero

            if iszero(
                call(
                    gas(),
                    pool, // pool
                    0x0,
                    ptr, // input selector
                    292, // input size = 164 (selector (4bytes) plus 5*32bytes)
                    ptr, // output
                    0x40 // output size = 0x40
                )
            ) {
                // Forward the error
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
            buyAmount := mload(add(ptr, 0x20))
            currentOffset := add(currentOffset, 21)
        }
        return (buyAmount, currentOffset);
    }
}
