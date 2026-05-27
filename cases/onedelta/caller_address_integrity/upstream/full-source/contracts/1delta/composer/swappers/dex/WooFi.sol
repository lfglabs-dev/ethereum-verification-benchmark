// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

// solhint-disable max-line-length

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title WooFi swapper contract
 */
abstract contract WooFiSwapper is ERC20Selectors, Masks {
    /// @dev WooFi rebate receiver
    address private constant REBATE_RECIPIENT = 0x0000000000000000000000000000000000000000;

    constructor() {}

    /**
     * Swaps exact input on WOOFi DEX
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 21     | 1              | pay flag             | <- 0: caller pays; 1: contract pays; greater: pre-funded
     */
    function _swapWooFiExactIn(
        uint256 fromAmount,
        address tokenIn,
        address tokenOut,
        address receiver,
        address callerAddress,
        uint256 currentOffset
    )
        internal
        returns (
            uint256 poolThenAmountOut,
            // first assign payFlag, then return offset
            uint256 payFlagCurrentOffset
        )
    {
        assembly {
            let ptr := mload(0x40)

            // load first 32 bytes
            poolThenAmountOut := calldataload(currentOffset)
            // pay flag extraction
            payFlagCurrentOffset := and(UINT8_MASK, shr(88, poolThenAmountOut))
            // get pool
            poolThenAmountOut := shr(96, poolThenAmountOut)
            switch lt(payFlagCurrentOffset, 2)
            case 1 {
                let success
                // payFlag evaluation
                switch payFlagCurrentOffset
                case 0 {
                    // selector for transferFrom(address,address,uint256)
                    mstore(ptr, ERC20_TRANSFER_FROM)
                    mstore(add(ptr, 0x04), callerAddress)
                    mstore(add(ptr, 0x24), poolThenAmountOut)
                    mstore(add(ptr, 0x44), fromAmount)
                    success := call(gas(), tokenIn, 0, ptr, 0x64, 0, 32)
                }
                // transfer plain
                case 1 {
                    // selector for transfer(address,uint256)
                    mstore(ptr, ERC20_TRANSFER)
                    mstore(add(ptr, 0x04), poolThenAmountOut)
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

            // selector for swap(address,address,uint256,uint256,address,address)
            mstore(
                ptr, //
                0x7dc2038200000000000000000000000000000000000000000000000000000000
            )
            mstore(add(ptr, 0x04), tokenIn)
            mstore(add(ptr, 0x24), tokenOut)
            mstore(add(ptr, 0x44), fromAmount)
            mstore(add(ptr, 0x64), 0x0) // amountOutMin unused
            mstore(add(ptr, 0x84), receiver) // recipient
            mstore(add(ptr, 0xA4), REBATE_RECIPIENT) // rebateTo
            if iszero(
                call(
                    gas(),
                    poolThenAmountOut,
                    0x0, // no native transfer
                    ptr,
                    0xC4, // input length 196
                    ptr, // store output here
                    0x20 // output is just uint
                )
            ) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
            // map amountOut to var
            poolThenAmountOut := mload(ptr)

            // skip 21 bytes
            payFlagCurrentOffset := add(currentOffset, 21)
        }

        return (poolThenAmountOut, payFlagCurrentOffset);
    }
}
