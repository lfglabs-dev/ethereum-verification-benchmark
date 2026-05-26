// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

// solhint-disable max-line-length

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title DodoV2 swapper contract
 */
abstract contract DodoV2Swapper is ERC20Selectors, Masks {
    /**
     * We need this to avoid stack too deep in the overall context
     * if `clLength<3` no flash loan will be executed,
     * othewise, we skip the funding transfers
     * 0 is pulling from caller
     * 1 is transferring from contract
     * 2 is pre-funded (meaning no transfers here)
     *
     */
    function _dodoPrepare(
        uint256 amountIn,
        address tokenIn,
        address callerAddress,
        uint256 currentOffset
    )
        private
        returns (uint256 dodoData, address pool, uint256 clLength)
    {
        assembly {
            dodoData := calldataload(currentOffset)
            pool := shr(96, dodoData)

            clLength := and(UINT16_MASK, shr(56, dodoData))

            let ptr := mload(0x40)
            // less than 2: funding via token transfers
            if lt(clLength, 2) {
                let success
                switch clLength
                case 0 {
                    // selector for transferFrom(address,address,uint256)
                    mstore(ptr, ERC20_TRANSFER_FROM)
                    mstore(add(ptr, 0x04), callerAddress)
                    mstore(add(ptr, 0x24), pool)
                    mstore(add(ptr, 0x44), amountIn)
                    success := call(gas(), tokenIn, 0, ptr, 0x64, 0, 32)
                }
                // transfer plain
                case 1 {
                    // selector for transfer(address,uint256)
                    mstore(ptr, ERC20_TRANSFER)
                    mstore(add(ptr, 0x04), pool)
                    mstore(add(ptr, 0x24), amountIn)
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
        }
    }

    /**
     * Swaps exact input on Dodo V2
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 1              | sellQuote            |
     * | 21     | 2              | pId                  | pool index for flash validation
     * | 22     | 2              | clLength / pay flag  | <- 0: caller pays; 1: contract pays; greater: pre-funded
     * | 25     | clLength       | calldata             | calldata for fash loan
     */
    function _swapDodoV2ExactIn(
        uint256 amountIn,
        address tokenIn,
        address tokenOut,
        address receiver,
        address callerAddress,
        uint256 currentOffset
    )
        internal
        returns (uint256 amountOut, uint256 clLength)
    {
        address pool;
        (amountOut, pool, clLength) = _dodoPrepare(
            amountIn,
            tokenIn,
            callerAddress, //
            currentOffset
        );
        assembly {
            let ptr := mload(0x40)
            // if it is a spot swap, it is already funded
            switch lt(clLength, 3)
            case 1 {
                // determine selector
                switch and(UINT8_MASK, shr(88, amountOut))
                case 0 {
                    // sellBase
                    mstore(0x0, 0xbd6015b400000000000000000000000000000000000000000000000000000000)
                }
                default {
                    // sellQuote
                    mstore(0x0, 0xdd93f59a00000000000000000000000000000000000000000000000000000000)
                }
                mstore(0x4, receiver)
                // call swap, revert if invalid/undefined pair
                if iszero(call(gas(), pool, 0x0, 0x0, 0x24, 0x0, 0x20)) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
                // the swap call returns the output amount directly
                amountOut := mload(0x0)
                // increment offset
                currentOffset := add(25, currentOffset)
            }
            // otherwise, execute flash loan
            default {
                let ptrAfter := add(ptr, 256)

                /**
                 * Similar to Uni V2 flash swaps
                 * We request the output amount and the other one is zero
                 */
                // flashLoan(
                //     uint256 baseAmount,
                //     uint256 quoteAmount,
                //     address assetTo,
                //     bytes calldata data
                // )

                // map data to the pool
                mstore(ptrAfter, 0xd0a494e400000000000000000000000000000000000000000000000000000000)
                /*
                 * Store the data for the callback as follows
                 * | Offset | Length (bytes) | Description          |
                 * |--------|----------------|----------------------|
                 * | 0      | 20             | caller               |
                 * | 20     | 20             | base                 |
                 * | 40     | 20             | quote                |
                 * | 60     | 2              | pId                  | <- we use calldatacopy from here
                 * | 62     | 2              | calldataLength       |
                 * | 64     | calldataLength | calldata             |
                 */

                // this is for the next call
                mstore(add(ptr, 0x24), amountIn)
                // determine selector
                switch and(UINT8_MASK, shr(88, amountOut))
                case 0 {
                    // querySellBase(address,uint256)
                    mstore(ptr, 0x79a0487600000000000000000000000000000000000000000000000000000000)
                    mstore(add(ptr, 0x4), 0) // trader is zero
                    // call pool
                    if iszero(
                        staticcall(
                            gas(),
                            pool,
                            ptr,
                            0x44, //
                            0,
                            0x20
                        )
                    ) {
                        returndatacopy(0, 0, returndatasize())
                        revert(0, returndatasize())
                    }
                    amountOut := mload(0)
                    // sell base -> input is base
                    mstore(add(ptrAfter, 4), 0)
                    mstore(add(ptrAfter, 36), amountOut)
                    // gap will be populated outside this
                    mstore(add(ptrAfter, 164), shl(96, callerAddress))
                    mstore(add(ptrAfter, 184), shl(96, tokenIn))
                    mstore(add(ptrAfter, 204), shl(96, tokenOut))
                }
                default {
                    // querySellQuote(address,uint256)
                    mstore(ptr, 0x66410a2100000000000000000000000000000000000000000000000000000000)
                    mstore(add(ptr, 0x4), 0) // trader is zero
                    // call pool
                    if iszero(
                        staticcall(
                            gas(),
                            pool,
                            ptr,
                            0x44, //
                            0,
                            0x20
                        )
                    ) {
                        returndatacopy(0, 0, returndatasize())
                        revert(0, returndatasize())
                    }
                    amountOut := mload(0)
                    // sell quote -> input is quote
                    mstore(add(ptrAfter, 4), amountOut)
                    mstore(add(ptrAfter, 36), 0)
                    // gap will be populated outside this
                    mstore(add(ptrAfter, 164), shl(96, callerAddress))
                    mstore(add(ptrAfter, 184), shl(96, tokenOut))
                    mstore(add(ptrAfter, 204), shl(96, tokenIn))
                }

                mstore(add(ptrAfter, 68), receiver) // (callback-) receiver - should be self
                mstore(add(ptrAfter, 100), 0x80) // bytes offset
                mstore(add(ptrAfter, 132), add(64, clLength)) // 3x address + pId + length

                calldatacopy(add(ptrAfter, 224), add(21, currentOffset), add(clLength, 4))

                // call swap, revert if invalid/undefined pair
                if iszero(
                    call(
                        gas(),
                        pool,
                        0x0,
                        ptrAfter,
                        add(228, clLength), //
                        0x0,
                        0x0
                    )
                ) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
                currentOffset := add(add(25, currentOffset), clLength)
            }
        }
        return (amountOut, currentOffset);
    }
}
