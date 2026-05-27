// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

// solhint-disable max-line-length

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title Uniswap V2 type swapper contract
 * @notice We do everything UniV2 here, incl Solidly, FoT, exactIn and -Out
 */
abstract contract V2TypeGeneric is ERC20Selectors, Masks {
    ////////////////////////////////////////////////////
    // Uni V2 type selctors
    ////////////////////////////////////////////////////

    /// @dev selector for getReserves()
    bytes32 private constant UNI_V2_GET_RESERVES = 0x0902f1ac00000000000000000000000000000000000000000000000000000000;

    /// @dev selector for swap(...)
    bytes32 private constant UNI_V2_SWAP = 0x022c0d9f00000000000000000000000000000000000000000000000000000000;

    /// @notice fixed selector transferFrom(...) on permit2
    bytes32 private constant PERMIT2_TRANSFER_FROM = 0x36c7851600000000000000000000000000000000000000000000000000000000;

    /// @notice deterministically deployed pemrit2 address
    address private constant PERMIT2 = 0x000000000022D473030F116dDEE9F6B43aC78BA3;

    /*
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 2              | feeDenom             |
     * | 22     | 1              | forkId               |
     * | 23     | 2              | calldataLength       | <-- 0: pay from self; 1: caller pays; 3: pre-funded;
     * | 25     | calldataLength | calldata             |
     */
    function _swapUniswapV2PoolExactInGeneric(
        uint256 amountIn,
        address tokenIn,
        address tokenOut,
        address receiver,
        uint256 currentOffset,
        address callerAddress
    )
        internal
        returns (
            uint256 buyAmount,
            // we need this as transient variable to not overflow the stacksize
            // the clLength is the calldata length for the callback at the beginning
            // and willl be used as the new incremented offset
            // this is to prevent `stack too deep` without using additional `mstore`
            uint256 clLength
        )
    {
        assembly {
            let ptr := mload(0x40) // free memory pointer
            ////////////////////////////////////////////////////
            // We extract all relevant data from the path bytes blob
            ////////////////////////////////////////////////////
            let pool := calldataload(currentOffset)
            clLength := and(UINT16_MASK, shr(56, pool))

            // Compute the buy amount based on the pair reserves.

            let zeroForOne :=
                lt(
                    tokenIn,
                    tokenOut //
                )

            switch lt(
                and(UINT8_MASK, shr(72, pool)), // this is the forkId
                128 // less than 128 indicates that it is classic uni V2, solidly otherwise
            )
            case 1 {
                // Pairs are in the range (0, 2¹¹²) so this shouldn't overflow.
                // buyAmount = (pairSellAmount * feeAm * buyReserve) /
                //     (pairSellAmount * feeAm + sellReserve * 10000);
                // this is expected to be 10000 - x, where x is the poolfee in bps
                let poolFeeDenom := and(shr(80, pool), UINT16_MASK)
                pool := shr(96, pool)

                // Call pair.getReserves(), store the results in scrap space
                mstore(0x0, UNI_V2_GET_RESERVES)
                if iszero(staticcall(gas(), pool, 0x0, 0x4, 0x0, 0x40)) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
                let reserveIn
                switch zeroForOne
                case 1 {
                    // Transpose if pair order is different.
                    buyAmount := mload(0x20)
                    reserveIn := mload(0x0)
                }
                default {
                    reserveIn := mload(0x20)
                    buyAmount := mload(0x0)
                }

                // compute out amount
                poolFeeDenom := mul(amountIn, poolFeeDenom)
                buyAmount :=
                    div(
                        mul(poolFeeDenom, buyAmount),
                        add(poolFeeDenom, mul(reserveIn, 10000)) //
                    )
            }
            // all solidly-based protocols
            default {
                // we ignore the fee denominator for solidly type DEXs
                pool := shr(96, pool)
                // selector for getAmountOut(uint256,address)
                mstore(ptr, 0xf140a35a00000000000000000000000000000000000000000000000000000000)
                mstore(add(ptr, 0x4), amountIn)
                mstore(add(ptr, 0x24), tokenIn)
                if iszero(staticcall(gas(), pool, ptr, 0x44, 0, 0x20)) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }

                buyAmount := mload(0)
            }

            ////////////////////////////////////////////////////
            // Prepare the swap tx
            ////////////////////////////////////////////////////

            // selector for swap(...)
            mstore(ptr, UNI_V2_SWAP)

            switch zeroForOne
            case 0 {
                mstore(add(ptr, 4), buyAmount)
                mstore(add(ptr, 36), 0)
            }
            default {
                mstore(add(ptr, 4), 0)
                mstore(add(ptr, 36), buyAmount)
            }
            mstore(add(ptr, 68), receiver)
            mstore(add(ptr, 100), 0x80) // bytes offset

            ////////////////////////////////////////////////////
            // This one is tricky:
            // if data length is > 3, we assume a flash swap and defer payment
            // if it is 0: we pull from caller,
            //          1: we pay from contract, and
            //          2: we assume pre-funding
            ////////////////////////////////////////////////////
            switch lt(clLength, 3)
            case 0 {
                /*
                 * Store the data for the callback as follows
                 * | Offset | Length (bytes) | Description          |
                 * |--------|----------------|----------------------|
                 * | 0      | 20             | caller               |
                 * | 20     | 20             | tokenIn              |
                 * | 40     | 20             | tokenOut             |
                 * | 60     | 1              | forkId               |
                 * | 61     | 2              | calldataLength       |
                 * | 63     | calldataLength | calldata             |
                 */
                mstore(add(ptr, 132), add(clLength, 63)) // calldataLength (within bytes)
                mstore(add(ptr, 164), shl(96, callerAddress))
                mstore(add(ptr, 184), shl(96, tokenIn))
                mstore(add(ptr, 204), shl(96, tokenOut))
                // we skip to the forkId offset
                currentOffset := add(22, currentOffset)
                // increment by 3 here (forkId, calldataLength)
                clLength := add(clLength, 3)
                // Store callback  (incl forkId)
                calldatacopy(add(ptr, 224), currentOffset, clLength)
                if iszero(
                    call(
                        gas(),
                        pool,
                        0x0,
                        ptr, // input selector
                        add(224, clLength), // 164 + (63+clLength)
                        0x0, // output = 0
                        0x0 // output size = 0
                    )
                ) {
                    // Forward the error
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
                // update clLength as new offset
                // we already added forkId and clLengh and datalength
                clLength := add(currentOffset, clLength)
            }
            ////////////////////////////////////////////////////
            // Otherwise, we have to assume that payment needs to
            // be facilitated outside the callback
            // 0: caller pays
            // 1: pay self
            // 2: the swap is pre-funded
            //    the operator needs to ensure that `amountIn`
            //    was already sent to the pool
            ////////////////////////////////////////////////////
            default {
                switch clLength
                case 0 {
                    // we need an incremented ptr here to not override the swap call below
                    clLength := add(ptr, 0xC4)
                    // selector for transferFrom(address,address,uint256)
                    mstore(clLength, ERC20_TRANSFER_FROM)
                    mstore(add(clLength, 0x04), callerAddress)
                    mstore(add(clLength, 0x24), pool)
                    mstore(add(clLength, 0x44), amountIn)

                    clLength := call(gas(), tokenIn, 0, clLength, 0x64, 0, 32)

                    let rdsize := returndatasize()

                    if iszero(
                        and(
                            clLength, // call itself succeeded
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
                // transfer plain
                case 1 {
                    // we need an incremented ptr here to not override the swap call below
                    clLength := add(ptr, 0xC4)
                    // selector for transfer(address,uint256)
                    mstore(clLength, ERC20_TRANSFER)
                    mstore(add(clLength, 0x04), pool)
                    mstore(add(clLength, 0x24), amountIn)
                    clLength := call(gas(), tokenIn, 0, clLength, 0x44, 0, 32)

                    let rdsize := returndatasize()

                    if iszero(
                        and(
                            clLength, // call itself succeeded
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
                ////////////////////////////////////////////////////
                // We store the bytes length to zero (no callback)
                // and directly trigger the swap
                ////////////////////////////////////////////////////
                mstore(add(ptr, 0x84), 0) // bytes length
                if iszero(call(gas(), pool, 0x0, ptr, 0xA4, 0, 0)) {
                    // Forward the error
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
                // update clLength as new offset
                clLength := add(currentOffset, 25)
            }
        }
        return (buyAmount, clLength);
    }

    /**
     * Executes an exact input swap internally across major UniV2 forks supporting
     * FOT tokens. Will only be used at the begining of a swap path where users sell a FOT token
     * Due to the nature of the V2 impleemntation, the callback is not triggered if no calldata is provided
     * As such, we never enter the callback implementation when using this function
     * @param amountIn sell amount
     * @return buyAmount output amount
     */
    function _swapUniV2ExactInFOTGeneric(
        uint256 amountIn,
        address tokenIn,
        address tokenOut,
        address receiver,
        uint256 currentOffset,
        address callerAddress
    )
        internal
        returns (uint256 buyAmount, uint256)
    {
        assembly {
            let ptr := mload(0x40) // free memory pointer

            ////////////////////////////////////////////////////
            // We extract all relevant data from the path bytes blob
            ////////////////////////////////////////////////////
            let pair := calldataload(currentOffset)

            // this is expected to be 10000 - x, where x is the poolfee in bps
            let poolFeeDenom := and(shr(80, pair), UINT16_MASK)

            // We only allow the caller to pay as otherwise, the fee is charged twice
            switch and(UINT16_MASK, shr(56, pair))
            case 0 {
                pair := shr(96, pair)
                // selector for transferFrom(address,address,uint256)
                mstore(ptr, ERC20_TRANSFER_FROM)
                mstore(add(ptr, 0x04), callerAddress)
                mstore(add(ptr, 0x24), pair)
                mstore(add(ptr, 0x44), amountIn)

                let success := call(gas(), tokenIn, 0, ptr, 0x64, 0, 32)

                let rdsize := returndatasize()
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
            case 1 {
                pair := shr(96, pair)
                // the 1-case here is a permit2 transfer
                // this is needed as FOT usually has no permit, meaning
                // direct permissioning is not possible
                // the "real" 1-case is not mixed up with the "regular" uni V2 case
                // as for FOT the intermediate holding of the asset cannot be facilitated
                mstore(ptr, PERMIT2_TRANSFER_FROM)
                mstore(add(ptr, 0x04), callerAddress)
                mstore(add(ptr, 0x24), pair)
                mstore(add(ptr, 0x44), amountIn)
                mstore(add(ptr, 0x64), tokenIn)
                if iszero(call(gas(), PERMIT2, 0, ptr, 0x84, 0x0, 0x0)) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
            }
            default { revert(0, 0) }

            // we define this as token in and later re-assign this to
            // reserve in to prevent stack too deep errors
            // Compute the buy amount based on the pair reserves.
            {
                let zeroForOne :=
                    lt(
                        tokenIn,
                        tokenOut // tokenOut
                    )
                // Pairs are in the range (0, 2¹¹²) so this shouldn't overflow.
                // buyAmount = (pairSellAmount * feeAm * buyReserve) /
                //     (pairSellAmount * feeAm + sellReserve * 1000);
                // Call pair.getReserves(), store the results in scrap space
                mstore(0x0, UNI_V2_GET_RESERVES)
                if iszero(staticcall(gas(), pair, 0x0, 0x4, 0x0, 0x40)) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
                // Revert if the pair contract does not return at least two words.
                if lt(returndatasize(), 0x40) { revert(0, 0) }
                let sellReserve
                switch zeroForOne
                case 1 {
                    // Transpose if pair order is different.
                    sellReserve := mload(0x0)
                    buyAmount := mload(0x20)
                }
                default {
                    sellReserve := mload(0x20)
                    buyAmount := mload(0x0)
                }
                // call tokenIn.balanceOf(pair)
                mstore(0x0, ERC20_BALANCE_OF)
                mstore(0x4, pair)
                // we store the result
                pop(staticcall(gas(), tokenIn, 0x0, 0x24, 0x0, 0x20))
                amountIn := sub(mload(0x0), sellReserve)

                // adjustment via denominator
                poolFeeDenom := mul(amountIn, poolFeeDenom)
                buyAmount := div(mul(poolFeeDenom, buyAmount), add(poolFeeDenom, mul(sellReserve, 10000)))

                ////////////////////////////////////////////////////
                // Prepare the swap tx
                ////////////////////////////////////////////////////

                // selector for swap(...)
                mstore(ptr, UNI_V2_SWAP)

                switch zeroForOne
                case 0 {
                    mstore(add(ptr, 0x4), buyAmount)
                    mstore(add(ptr, 0x24), 0)
                }
                default {
                    mstore(add(ptr, 0x4), 0)
                    mstore(add(ptr, 0x24), buyAmount)
                }
                mstore(add(ptr, 0x44), receiver)
                mstore(add(ptr, 0x64), 0x80) // bytes offset

                ////////////////////////////////////////////////////
                // We store the bytes length to zero (no callback)
                // and directly trigger the swap
                ////////////////////////////////////////////////////
                mstore(add(ptr, 0x84), 0) // bytes length
                if iszero(call(gas(), pair, 0x0, ptr, 0xA4, 0, 0)) {
                    // Forward the error
                    returndatacopy(0, 0, returndatasize())
                    revert(0, returndatasize())
                }
            }
            // update clLength as new offset
            currentOffset := add(currentOffset, 25)
        }
        return (buyAmount, currentOffset);
    }
}
