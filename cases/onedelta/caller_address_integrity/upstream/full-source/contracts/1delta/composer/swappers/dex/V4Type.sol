// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title Uniswap V4 type swapper contract
 * @notice Can only be executed within `manager.unlock()`
 * Ergo, if Uniswap v4 is in the path (no matter how many times), one has to push
 * the swap data and execution into the UniswapV4.unlock
 * This should be usable together with flash loans from their singleton
 *
 * Cannot unlock multiple times!
 *
 * The execution of a swap follows the steps:
 *
 * 1) pm.unlock(...) (outside of this contract)
 * 2) call pm.swap(...)
 * 3) getDeltas via pm.exttload(bytes[]) (we get it for input/output at once)
 *    we get [inputDelta, outputDelta] (pay amount, receive amount)
 *    As for the V4 docs, `swap` does not necessarily return the correct
 *    deltas when using hooks, that is why we remain with fetching the deltas
 * 4) call pm.take to pull the outputDelta from pm
 * 4) if input nonnative call pm.sync() and send inputDelta to pm
 * 5) call pm.settle to settle the swap (if native with input value)
 *
 * Technically it is possible to call multihops within V4 where one would
 * skip the `take` when the next swap is also for V4
 * This is a bit annoying to implement and for this first version we skip it
 */
abstract contract V4TypeGeneric is ERC20Selectors, Masks {
    /**
     * We need all these selectors for executing a single swap
     */
    bytes32 private constant SWAP = 0xf3cd914c00000000000000000000000000000000000000000000000000000000;
    bytes32 private constant TAKE = 0x0b0d9c0900000000000000000000000000000000000000000000000000000000;
    bytes32 private constant SETTLE = 0x11da60b400000000000000000000000000000000000000000000000000000000;
    bytes32 private constant SYNC = 0xa584119400000000000000000000000000000000000000000000000000000000;
    bytes32 private constant EXTTLOAD = 0x9bf6645f00000000000000000000000000000000000000000000000000000000;

    constructor() {}

    /*
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | hooks                |
     * | 20     | 20             | manager              |
     * | 40     | 3              | fee                  |
     * | 43     | 3              | tickSpacing          |
     * | 46     | 1              | payFlag              |
     * | 47     | 2              | calldataLength       |
     * | 49     | calldataLength | calldata             |
     */
    function _swapUniswapV4ExactInGeneric(
        uint256 fromAmount,
        address tokenIn,
        address tokenOut,
        address receiver,
        uint256 currentOffset,
        address callerAddress
    )
        internal
        returns (
            // this var changes from zeroToOne to the received amount
            uint256 receivedAmount,
            // similar to other implementations, we use this temp variable
            // to avoid stackToo deep
            uint256 tempVar
        )
    {
        // struct PoolKey {
        //     address currency0; 4
        //     address currency1; 36
        //     uint24 fee; 68
        //     int24 tickSpacing; 100
        //     address hooks; 132
        // }
        // struct SwapParams {
        //     bool zeroForOne; 164
        //     int256 amountSpecified; 196
        //     uint160 sqrtPriceLimitX96; 228
        // }
        ////////////////////////////////////////////
        // This is the function selector we need
        ////////////////////////////////////////////
        //  swap(
        //        PoolKey memory key,
        //        SwapParams memory params,
        //        bytes calldata hookData //
        //     )

        // solhint-disable-next-line no-inline-assembly
        assembly {
            let ptr := mload(0x40)

            // read the pool address
            let pool := calldataload(add(currentOffset, 20))

            // let tickSpacing := and(UINT24_MASK, shr(48, pool))
            // pay flag
            tempVar := and(UINT8_MASK, shr(40, pool))
            let clLength := and(UINT16_MASK, shr(24, pool))

            // Prepare external call data
            // Store swap selector
            mstore(ptr, SWAP)

            /**
             * PoolKey  (2/2)
             */

            // Store fee
            mstore(add(ptr, 68), and(UINT24_MASK, shr(72, pool)))

            // Store tickSpacing
            mstore(add(ptr, 100), and(UINT24_MASK, shr(48, pool)))

            // get the hook
            let hook := shr(96, calldataload(currentOffset))
            mstore(add(ptr, 132), hook)

            pool := shr(96, pool)

            // Store data offset
            mstore(add(ptr, 260), 0x120)
            // Store data length
            mstore(add(ptr, 292), clLength)

            /**
             * SwapParams
             */

            // Store fromAmount
            mstore(add(ptr, 196), sub(0, fromAmount))

            // skip pool plus params
            currentOffset := add(currentOffset, 49)
            if xor(0, clLength) {
                // Store furhter calldata (add 4 to length due to fee and clLength)
                calldatacopy(add(ptr, 324), currentOffset, clLength)
            }

            // use receivedAmount as zeroForOne
            receivedAmount := lt(tokenIn, tokenOut)
            // Store zeroForOne
            mstore(add(ptr, 164), receivedAmount)
            // store pool key and limits
            switch receivedAmount
            // zeroForOne
            case 1 {
                /**
                 * PoolKey  (1/2)
                 */

                // Store ccy0
                mstore(add(ptr, 4), tokenIn)
                // Store ccy1
                mstore(add(ptr, 36), tokenOut)

                // Store sqrtPriceLimitX96
                mstore(add(ptr, 228), MIN_SQRT_RATIO)
            }
            default {
                /**
                 * PoolKey  (1/2)
                 */

                // Store ccy0
                mstore(add(ptr, 4), tokenOut)
                // Store ccy1
                mstore(add(ptr, 36), tokenIn)

                // Store sqrtPriceLimitX96
                mstore(add(ptr, 228), MAX_SQRT_RATIO)
            }

            // Perform the external 'swap' call
            if iszero(call(gas(), pool, 0, ptr, add(324, clLength), 0, 0x20)) {
                // store return value directly to free memory pointer
                // The call failed; we retrieve the exact error message and revert with it
                returndatacopy(0, 0, returndatasize()) // Copy the error message to the start of memory
                revert(0, returndatasize()) // Revert with the error message
            }

            // if no hook provided, read plain swap, otherwise, read deltas
            switch iszero(hook)
            case 1 {
                fromAmount := mload(0)
                switch receivedAmount
                case 1 {
                    receivedAmount := and(UINT128_MASK, fromAmount)
                    fromAmount := sub(0, sar(128, fromAmount))
                }
                default {
                    receivedAmount := shr(128, fromAmount)
                    fromAmount := sub(0, signextend(15, fromAmount))
                }
            }
            default {
                /**
                 * Load actual deltas from pool manager if hook provided
                 * This is recommended in the docs
                 */
                mstore(ptr, EXTTLOAD)
                mstore(add(ptr, 4), 0x20) // offset
                mstore(add(ptr, 36), 2) // array length

                mstore(0, address())
                mstore(0x20, tokenIn)
                // first key
                mstore(add(ptr, 68), keccak256(0, 0x40))
                // output token for 2nd key
                mstore(0x20, tokenOut)
                // second key
                mstore(add(ptr, 100), keccak256(0, 0x40))

                // get the deltas
                pop(
                    staticcall(
                        gas(),
                        pool,
                        ptr,
                        132, // selector + offs + length + key0 + key1
                        ptr,
                        0x80 // output (offset, length, data0, data1)
                    )
                )

                // 1st array output element
                fromAmount := sub(0, mload(add(ptr, 0x40)))
                // 2nd array output element
                receivedAmount := mload(add(ptr, 0x60))
            }

            /**
             * Pull funds to receiver
             */
            mstore(ptr, TAKE)
            mstore(add(ptr, 4), tokenOut) //
            mstore(add(ptr, 36), receiver)
            mstore(add(ptr, 68), receivedAmount)

            if iszero(
                call(
                    gas(),
                    pool,
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

            /**
             * If the pay mode is >=2, we assume deferred payment
             * This means that the composer must manually settle
             * for the input amount
             * Warning: This should not be done for pools with
             * arbitrary hooks as these can have cases where
             * `amountIn` selected != actual `amountIn`
             */
            if lt(tempVar, 2) {
                /**
                 * Pull funds from payer
                 */
                switch iszero(tokenIn)
                // nonnative
                case 0 {
                    /**
                     * Sync pay asset
                     */
                    mstore(0, SYNC)
                    mstore(4, tokenIn) // offset

                    if iszero(
                        call(
                            gas(),
                            pool,
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

                    {
                        // temp var is the pay mode and then succes flag
                        switch tempVar
                        case 0 {
                            // selector for transferFrom(address,address,uint256)
                            mstore(ptr, ERC20_TRANSFER_FROM)
                            mstore(add(ptr, 0x04), callerAddress)
                            mstore(add(ptr, 0x24), pool)
                            mstore(add(ptr, 0x44), fromAmount)
                            tempVar := call(gas(), tokenIn, 0, ptr, 0x64, 0, 32)
                        }
                        // transfer plain
                        case 1 {
                            // selector for transfer(address,uint256)
                            mstore(ptr, ERC20_TRANSFER)
                            mstore(add(ptr, 0x04), pool)
                            mstore(add(ptr, 0x24), fromAmount)
                            tempVar := call(gas(), tokenIn, 0, ptr, 0x44, 0, 32)
                        }

                        let rdsize := returndatasize()

                        if iszero(
                            and(
                                tempVar, // call itself succeeded
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
                    // we continue to use it as native value
                    // zero for erc20 transfer
                    tempVar := 0
                }
                // native (temVar is the fromAmount)
                default { tempVar := fromAmount }
                /**
                 * Settle funds in pool manager
                 */

                // settle amount
                mstore(0, SETTLE)
                if iszero(
                    call(
                        gas(),
                        pool,
                        tempVar,
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
        }
        return (receivedAmount, currentOffset);
    }
}
