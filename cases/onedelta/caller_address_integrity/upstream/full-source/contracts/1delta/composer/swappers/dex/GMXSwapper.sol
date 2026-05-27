// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title GMX V1 swapper, works for most forks, too
 */
abstract contract GMXSwapper is ERC20Selectors, Masks {
    /**
     * Swaps exact input on GMX V1
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 1              | pay flag             | <- 0: caller pays; 1: contract pays; greater: pre-funded
     */
    function _swapGMXExactIn(
        uint256 fromAmount,
        address tokenIn,
        address tokenOut,
        address receiver, //
        address callerAddress,
        uint256 currentOffset
    )
        internal
        returns (uint256 amountOut, uint256)
    {
        assembly {
            let ptr := mload(0x40)

            let gmxData := calldataload(currentOffset)
            let vault := shr(96, gmxData)

            switch and(UINT8_MASK, shr(88, gmxData))
            case 0 {
                // selector for transferFrom(address,address,uint256)
                mstore(ptr, ERC20_TRANSFER_FROM)
                mstore(add(ptr, 0x04), callerAddress)
                mstore(add(ptr, 0x24), vault)
                mstore(add(ptr, 0x44), fromAmount)

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
            // transfer plain
            case 1 {
                // selector for transfer(address,uint256)
                mstore(ptr, ERC20_TRANSFER)
                mstore(add(ptr, 0x04), vault)
                mstore(add(ptr, 0x24), fromAmount)
                let success := call(gas(), tokenIn, 0, ptr, 0x44, 0, 32)

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

            // selector for swap(address,address,address)
            mstore(
                ptr, //
                0x9331621200000000000000000000000000000000000000000000000000000000
            )
            mstore(add(ptr, 0x04), tokenIn)
            mstore(add(ptr, 0x24), tokenOut)
            mstore(add(ptr, 0x44), receiver)
            if iszero(
                call(
                    gas(),
                    vault,
                    0x0, // no native transfer
                    ptr,
                    0x64, // input length 66 bytes
                    ptr, // store output here
                    0x20 // output is just uint
                )
            ) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }

            amountOut := mload(ptr)
            currentOffset := add(currentOffset, 21)
        }
        return (amountOut, currentOffset);
    }
}
