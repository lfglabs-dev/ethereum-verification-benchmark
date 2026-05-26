// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

// solhint-disable max-line-length

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title Balancer V3 type swapper contract
 * @notice Can only be executed within `manager.unlock()`
 * Ergo, if Balancer v3 is in the path (no matter how many times), one has to push
 * the swap data and execution into the BalancerV3.unlock
 * This should be usable together with flash loans from their singleton
 *
 * Can unlock arbitrary times times!
 *
 * The execution of a swap follows the steps:
 *
 * 1) pm.unlock(...) (outside of this contract)
 * 2) call pm.swap(...)
 * 3) call pm.settle to settle the swap (no native accepted)
 *
 */
abstract contract BalancerV3Swapper is ERC20Selectors, Masks {
    /**
     * We need all these selectors for executing a single swap
     */
    bytes32 private constant SWAP = 0x2bfb780c00000000000000000000000000000000000000000000000000000000;
    /// @notice same selector string name as for UniV4, different params for balancer
    bytes32 private constant SETTLE = 0x15afd40900000000000000000000000000000000000000000000000000000000;
    /// @notice pull funds from vault with this
    bytes32 private constant SEND_TO = 0xae63932900000000000000000000000000000000000000000000000000000000;

    constructor() {}

    /*
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 20             | manager              |
     * | 40     | 1              | payFlag              |
     * | 41     | 2              | calldataLength       | <- this here might be pool-dependent, cannot be used as flag
     * | 43     | calldataLength | calldata             |
     */
    function _swapBalancerV3ExactInGeneric(
        uint256 fromAmount,
        address tokenIn,
        address tokenOut,
        address receiver,
        uint256 currentOffset,
        address callerAddress
    )
        internal
        returns (
            uint256 receivedAmount,
            // similar to other implementations, we use this temp variable
            // to avoid stackToo deep
            uint256 tempVar
        )
    {
        // enum SwapKind {
        //     EXACT_IN,
        //     EXACT_OUT
        // }
        // struct VaultSwapParams {
        //     SwapKind kind; 4
        //     address pool; 36
        //     IERC20 tokenIn; 68
        //     IERC20 tokenOut; 100
        //     uint256 amountGivenRaw; 132
        //     uint256 limitRaw; 164
        //     bytes userData; (196, 228, 260 - X)
        // }
        ////////////////////////////////////////////
        // This is the function selector we need
        ////////////////////////////////////////////
        // function swap(
        //     VaultSwapParams memory vaultSwapParams
        // )
        //     external
        //     returns (uint256 amountCalculated, uint256 amountIn, uint256 amountOut)

        // solhint-disable-next-line no-inline-assembly
        assembly {
            let ptr := mload(0x40)
            // read the hook address and insta store it to keep stack smaller
            mstore(add(ptr, 132), shr(96, calldataload(currentOffset)))
            let pool := shr(96, calldataload(currentOffset))
            // skip hook
            currentOffset := add(currentOffset, 20)
            // read the pool address
            let vault := calldataload(currentOffset)
            // skip vault plus params
            currentOffset := add(currentOffset, 23)

            // pay flag
            tempVar := and(UINT8_MASK, shr(88, vault))
            let clLength := and(UINT16_MASK, shr(72, vault))
            vault := shr(96, vault)
            // Prepare external call data
            // Store swap selector
            mstore(ptr, SWAP)
            mstore(add(ptr, 4), 0)
            mstore(add(ptr, 36), pool)
            mstore(add(ptr, 68), tokenIn)
            mstore(add(ptr, 100), tokenOut)
            mstore(add(ptr, 132), fromAmount)
            mstore(add(ptr, 164), 1)
            mstore(add(ptr, 196), 0xe0)
            mstore(add(ptr, 228), clLength)

            if xor(0, clLength) {
                // Store further calldata for the pool
                calldatacopy(add(ptr, 260), currentOffset, clLength)
                currentOffset := add(currentOffset, clLength)
            }
            // Perform the external 'swap' call
            if iszero(call(gas(), vault, 0, ptr, add(260, clLength), ptr, 0x60)) {
                returndatacopy(0, 0, returndatasize()) // Copy the error message to the start of memory
                revert(0, returndatasize()) // Revert with the error message
            }

            // get real amounts
            fromAmount := mload(add(ptr, 0x20))
            receivedAmount := mload(add(ptr, 0x40))

            /**
             * Pull funds to receiver
             */
            mstore(ptr, SEND_TO)
            mstore(add(ptr, 4), tokenOut) //
            mstore(add(ptr, 36), receiver)
            mstore(add(ptr, 68), receivedAmount)

            if iszero(
                call(
                    gas(),
                    vault,
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
             * If the pay mode is >=3, we assume deferred payment
             * This means that the composer must manually settle
             * for the input amount
             * Warning: This should not be done for pools with
             * arbitrary hooks as these can have cases where
             * `amountIn` selected != actual `amountIn`
             */
            if lt(tempVar, 2) {
                let success
                switch tempVar
                case 0 {
                    // selector for transferFrom(address,address,uint256)
                    mstore(ptr, ERC20_TRANSFER_FROM)
                    mstore(add(ptr, 0x04), callerAddress)
                    mstore(add(ptr, 0x24), vault)
                    mstore(add(ptr, 0x44), fromAmount)
                    success := call(gas(), tokenIn, 0, ptr, 0x64, 0, 32)
                }
                // transfer plain
                case 1 {
                    // selector for transfer(address,uint256)
                    mstore(ptr, ERC20_TRANSFER)
                    mstore(add(ptr, 0x04), vault)
                    mstore(add(ptr, 0x24), fromAmount)
                    success := call(gas(), tokenIn, 0, ptr, 0x44, 0, 32)
                }

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

                /**
                 * Settle funds in vault
                 */

                // settle amount
                mstore(ptr, SETTLE)
                mstore(add(ptr, 4), tokenIn)
                mstore(add(ptr, 36), fromAmount)
                if iszero(
                    call(
                        gas(),
                        vault,
                        0x0, // no native
                        ptr,
                        68,
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
