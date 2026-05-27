// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

// solhint-disable max-line-length

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title Curve swapper contract
 * @notice We do Curve stuff here
 */
abstract contract CurveSwapper is ERC20Selectors, Masks {
    // approval slot
    bytes32 private constant CALL_MANAGEMENT_APPROVALS = 0x1aae13105d9b6581c36534caba5708726e5ea1e03175e823c989a5756966d1f3;

    /**
     * Standard curve pool selectors
     */

    ////////////////////////////////////////////////////
    // General info on the selectors for Curve:
    // There are 5 variations
    // 1) indexes as int128
    // 2) indexes as uint256
    // 3) has receiver
    // 4) has no receiver
    // 5) fork with solidity implementation (typically uint8 indexes)
    // The int128 indexes are preferred and have lower indexes
    // The ones with receiver have even indexes
    ////////////////////////////////////////////////////

    /// @notice selector exchange(int128,int128,uint256,uint256)
    bytes32 private constant EXCHANGE_INT = 0x3df0212400000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange(int128,int128,uint256,uint256,address)
    bytes32 private constant EXCHANGE_INT_WITH_RECEIVER = 0xddc1f59d00000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange(uint256,uint256,uint256,uint256)
    bytes32 private constant EXCHANGE = 0x5b41b90800000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange(uint256,uint256,uint256,uint256,address)
    bytes32 private constant EXCHANGE_WITH_RECEIVER = 0xa64833a000000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange_underlying(uint256,uint256,uint256,uint256)
    bytes32 private constant EXCHANGE_UNDERLYING = 0x65b2489b00000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange_underlying(uint256,uint256,uint256,uint256,address)
    bytes32 private constant EXCHANGE_UNDERLYING_WITH_RECEIVER = 0xe2ad025a00000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange_underlying(uint256,uint256,uint256,uint256)
    bytes32 private constant EXCHANGE_UNDERLYING_INT = 0xa6417ed600000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange_underlying(uint256,uint256,uint256,uint256,address)
    bytes32 private constant EXCHANGE_UNDERLYING_INT_WITH_RECEIVER = 0x44ee198600000000000000000000000000000000000000000000000000000000;

    ////////////////////////////////////////////////////
    // General info on the selectors for Curve Received:
    // They are pre-funded
    // 1) indexes as int128 (NG) or uint256 (Some of the TriCryptos) as above
    // 2) has always a receiver (optinally could be called without it, bet there is no utility for it)
    ////////////////////////////////////////////////////

    /// @notice selector exchange_received(uint256,uint256,uint256,uint256)
    bytes32 private constant EXCHANGE_RECEIVED = 0x29b244bb00000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange_received(uint256,uint256,uint256,uint256,address)
    bytes32 private constant EXCHANGE_RECEIVED_WITH_RECEIVER = 0x767691e700000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange(int128,int128,uint256,uint256)
    bytes32 private constant EXCHANGE_RECEIVED_INT = 0x7e3db03000000000000000000000000000000000000000000000000000000000;

    /// @notice selector exchange_received(int128,int128,uint256,uint256,address)
    bytes32 private constant EXCHANGE_RECEIVED_INT_WITH_RECEIVER = 0xafb4301200000000000000000000000000000000000000000000000000000000;

    /// @notice selector for cuve forks using solidity swap(uint8,uint8,uint256,uint256,uint256)
    bytes32 private constant SWAP = 0x9169558600000000000000000000000000000000000000000000000000000000;

    function _fundAndApproveIfNeeded(address callerAddress, address tokenIn, uint256 amount, uint256 data) private returns (address pool) {
        assembly {
            let ptr := mload(0x40)
            pool := shr(96, data)
            mstore(0x0, tokenIn)
            mstore(0x20, CALL_MANAGEMENT_APPROVALS)
            mstore(0x20, keccak256(0x0, 0x40))
            mstore(0x0, pool)
            let key := keccak256(0x0, 0x40)
            // check if already approved
            if iszero(sload(key)) {
                // approveFlag
                // selector for approve(address,uint256)
                mstore(ptr, ERC20_APPROVE)
                mstore(add(ptr, 0x04), pool)
                mstore(add(ptr, 0x24), MAX_UINT256)
                pop(
                    call(
                        gas(),
                        tokenIn, //
                        0,
                        ptr,
                        0x44,
                        ptr,
                        32
                    )
                )
                sstore(key, 1)
            }
            if iszero(and(UINT16_MASK, shr(56, data))) {
                // selector for transferFrom(address,address,uint256)
                mstore(ptr, ERC20_TRANSFER_FROM)
                mstore(add(ptr, 0x04), callerAddress)
                mstore(add(ptr, 0x24), address())
                mstore(add(ptr, 0x44), amount)

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
        }
    }

    /**
     * Swaps using a standard curve pool
     * Data is supposed to be packed as follows
     * tokenIn | actionId | dexId | pool | i | j | sm | tokenOut
     * sm is the selector,
     * i,j are the swap indexes for the pool
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 1              | i                    |
     * | 21     | 1              | j                    |
     * | 22     | 1              | sm                   |
     * | 23     | 2              | payMode              | <-- 0: pay from self; 1: caller pays; 3: pre-funded;
     */
    function _swapCurveGeneral(
        address tokenIn,
        address tokenOut,
        uint256 amountIn,
        address receiver, //
        address callerAddress,
        uint256 currentOffset
    )
        internal
        returns (
            uint256 amountOut,
            // curve data is a transient memory variable to
            // avoid stack too deep errors
            uint256 curveData
        )
    {
        address pool;
        assembly {
            curveData := calldataload(currentOffset)
        }
        // extract pool
        pool = _fundAndApproveIfNeeded(
            callerAddress,
            tokenIn,
            amountIn,
            curveData // use generic data
        );
        assembly {
            let ptr := mload(0x40)

            // consistent params not overlapping with 32 bytes from selector
            mstore(add(ptr, 0x24), and(shr(80, curveData), UINT8_MASK))
            mstore(add(ptr, 0x44), amountIn)
            mstore(add(ptr, 0x64), 0) // min out

            let success
            ////////////////////////////////////////////////////
            // Execute swap function
            ////////////////////////////////////////////////////
            switch and(shr(72, curveData), UINT8_MASK)
            // selectorId
            case 0 {
                // selector for exchange(int128,int128,uint256,uint256,address)
                mstore(ptr, EXCHANGE_INT_WITH_RECEIVER)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
                mstore(add(ptr, 0x84), receiver) // receiver, set curveData accordingly
                success := call(gas(), pool, 0x0, ptr, 0xA4, ptr, 0x20)
                curveData := 0
            }
            case 1 {
                // selector for exchange(int128,int128,uint256,uint256)
                mstore(ptr, EXCHANGE_INT)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
                success := call(gas(), pool, 0x0, ptr, 0x84, ptr, 0x20)
                curveData := MAX_UINT256
            }
            case 2 {
                // selector for exchange(uint256,uint256,uint256,uint256,address)
                mstore(ptr, EXCHANGE_WITH_RECEIVER)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
                mstore(add(ptr, 0x84), receiver) // receiver, set curveData accordingly
                success := call(gas(), pool, 0x0, ptr, 0xA4, ptr, 0x20)
                curveData := 0
            }
            case 3 {
                // selector for exchange(uint256,uint256,uint256,uint256)
                mstore(ptr, EXCHANGE)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))

                success := call(gas(), pool, 0x0, ptr, 0x84, ptr, 0x20)
                curveData := MAX_UINT256
            }
            case 4 {
                // selector for exchange_underlying(int128,int128,uint256,uint256,address)
                mstore(ptr, EXCHANGE_UNDERLYING_INT_WITH_RECEIVER)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
                mstore(add(ptr, 0x84), receiver)
                success := call(gas(), pool, 0x0, ptr, 0xA4, ptr, 0x20)
                curveData := 0
            }
            case 5 {
                // selector for exchange_underlying(int128,int128,uint256,uint256)
                mstore(ptr, EXCHANGE_UNDERLYING_INT)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
                success := call(gas(), pool, 0x0, ptr, 0x84, ptr, 0x20)
                curveData := MAX_UINT256
            }
            case 6 {
                // selector for exchange_underlying(uint256,uint256,uint256,uint256,address)
                mstore(ptr, EXCHANGE_UNDERLYING_WITH_RECEIVER)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
                mstore(add(ptr, 0x84), receiver)
                success := call(gas(), pool, 0x0, ptr, 0xA4, ptr, 0x20)
                curveData := 0
            }
            case 7 {
                // selector for exchange_underlying(uint256,uint256,uint256,uint256)
                mstore(ptr, EXCHANGE_UNDERLYING)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
                success := call(gas(), pool, 0x0, ptr, 0x84, ptr, 0x20)
                curveData := MAX_UINT256
            }
            case 200 {
                // selector for swap(uint8,uint8,uint256,uint256,uint256)
                mstore(ptr, SWAP)
                mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
                mstore(add(ptr, 0x84), MAX_UINT256) // deadline
                success := call(gas(), pool, 0x0, ptr, 0xA4, ptr, 0x20)
                curveData := MAX_UINT256
            }
            default { revert(0, 0) }

            if iszero(success) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }

            amountOut := mload(ptr)

            ////////////////////////////////////////////////////
            // Send funds to receiver if needed
            // curveData is now the flag for manually
            // transferuing to the receiver
            ////////////////////////////////////////////////////
            if and(curveData, xor(receiver, address())) {
                // selector for transfer(address,uint256)
                mstore(ptr, ERC20_TRANSFER)
                mstore(add(ptr, 0x04), receiver)
                mstore(add(ptr, 0x24), amountOut)
                success := call(gas(), tokenOut, 0, ptr, 0x44, 0, 32)

                let rdsize := returndatasize()

                // Check for ERC20 success. ERC20 tokens should return a boolean,
                // but some don't. We accept 0-length return data as success, or at
                // least 32 bytes that starts with a 32-byte boolean true.
                success :=
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

                if iszero(success) {
                    returndatacopy(0, 0, rdsize)
                    revert(0, rdsize)
                }
            }
            curveData := add(currentOffset, 25)
        }
        return (amountOut, curveData);
    }

    /**
     * Swaps using a standard curve pool
     * Data is supposed to be packed as follows
     * tokenIn | actionId | dexId | pool | i | j | sm | tokenOut
     * sm is the selector,
     * i,j are the swap indexes for the pool
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 1              | i                    |
     * | 21     | 1              | j                    |
     * | 22     | 1              | sm                   |
     * | 23     | 2              | payMode              | <-- 0: pay from self; 1: caller pays; 3: pre-funded;
     */
    function _swapCurveFork(
        address tokenIn,
        address tokenOut,
        uint256 amountIn,
        address receiver, //
        address callerAddress,
        uint256 currentOffset
    )
        internal
        returns (
            uint256 amountOut,
            // curve data is a transient memory variable to
            // avoid stack too deep errors
            uint256 curveData
        )
    {
        address pool;
        assembly {
            curveData := calldataload(currentOffset)
        }
        // extract pool
        pool = _fundAndApproveIfNeeded(
            callerAddress,
            tokenIn,
            amountIn,
            curveData // use generic data
        );
        assembly {
            let ptr := mload(0x40)

            mstore(0x0, ERC20_BALANCE_OF)
            mstore(0x4, address())
            // call to token
            pop(
                staticcall(
                    gas(),
                    tokenOut, // token
                    0x0,
                    0x24,
                    ptr, // use ptr here so that we don't override the scrap space
                    0x20
                )
            )

            amountOut := mload(ptr)

            ////////////////////////////////////////////////////
            // Execute swap function
            ////////////////////////////////////////////////////

            // get selector
            switch and(shr(72, curveData), UINT8_MASK)
            // selectorId
            case 3 {
                // selector for exchange(int128,int128,uint256,uint256,address)
                mstore(ptr, EXCHANGE)
            }
            case 5 {
                // selector for exchange(int128,int128,uint256,uint256)
                mstore(ptr, EXCHANGE_UNDERLYING)
            }
            default { revert(0, 0) }

            mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK))
            mstore(add(ptr, 0x24), and(shr(80, curveData), UINT8_MASK))
            mstore(add(ptr, 0x44), amountIn)
            mstore(add(ptr, 0x64), 0) // min out
            if iszero(call(gas(), pool, 0x0, ptr, 0x84, 0x0, 0x0)) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }

            // call to token - note that 0x-0x24 still holds the respective calldata
            pop(
                staticcall(
                    gas(),
                    tokenOut, // token
                    0x0,
                    0x24,
                    0x0, // output to ptr
                    0x20
                )
            )
            // load the retrieved balance
            amountOut := sub(mload(0x0), amountOut)

            ////////////////////////////////////////////////////
            // Send funds to receiver if needed
            ////////////////////////////////////////////////////
            if xor(receiver, address()) {
                // selector for transfer(address,uint256)
                mstore(ptr, ERC20_TRANSFER)
                mstore(add(ptr, 0x04), receiver)
                mstore(add(ptr, 0x24), amountOut)
                let success :=
                    call(
                        gas(),
                        tokenOut, // tokenIn, pool + 5x uint8 (i,j,s,a)
                        0,
                        ptr,
                        0x44,
                        ptr,
                        32
                    )

                let rdsize := returndatasize()

                // Check for ERC20 success. ERC20 tokens should return a boolean,
                // but some don't. We accept 0-length return data as success, or at
                // least 32 bytes that starts with a 32-byte boolean true.
                success :=
                    and(
                        success, // call itself succeeded
                        or(
                            iszero(rdsize), // no return data, or
                            and(
                                gt(rdsize, 31), // at least 32 bytes
                                eq(mload(ptr), 1) // starts with uint256(1)
                            )
                        )
                    )

                if iszero(success) {
                    returndatacopy(0, 0, rdsize)
                    revert(0, rdsize)
                }
            }
            curveData := add(currentOffset, 25)
        }
        return (amountOut, curveData);
    }

    /**
     * Swaps using a NG pool that allows for pre-funded swaps
     * Data is supposed to be packed as follows
     * tokenIn | actionId | dexId | pool | sm | i | j | tokenOut
     * sm is the selector,
     * i,j are the swap indexes for the pool
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | pool                 |
     * | 20     | 1              | i                    |
     * | 21     | 1              | j                    |
     * | 22     | 1              | sm                   |
     * | 23     | 2              | payMode              | <-- 0: pay from self; 1: caller pays; 3: pre-funded;
     */
    function _swapCurveReceived(
        address tokenIn,
        uint256 amountIn,
        address receiver, //
        address callerAddress,
        uint256 currentOffset
    )
        internal
        returns (
            // assign payFlag then amountOut
            uint256 payFlagAmountOut,
            uint256 curveData
        )
    {
        assembly {
            let ptr := mload(0x40)
            curveData := calldataload(currentOffset)

            let pool := shr(96, curveData)

            payFlagAmountOut := and(UINT16_MASK, shr(56, curveData))
            if lt(payFlagAmountOut, 2) {
                let success
                switch payFlagAmountOut
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
            ////////////////////////////////////////////////////
            // Execute swap function
            ////////////////////////////////////////////////////
            switch and(shr(72, curveData), UINT8_MASK)
            case 0 {
                // selector for exchange_received(int128,int128,uint256,uint256,address)
                mstore(ptr, EXCHANGE_RECEIVED_INT_WITH_RECEIVER)
            }
            case 2 {
                // selector for exchange_received(uint256,uint256,uint256,uint256,address)
                mstore(ptr, EXCHANGE_RECEIVED_WITH_RECEIVER)
            }
            default { revert(0, 0) }

            mstore(add(ptr, 0x4), and(shr(88, curveData), UINT8_MASK)) // indexIn
            mstore(add(ptr, 0x24), and(shr(80, curveData), UINT8_MASK)) // indexOut
            mstore(add(ptr, 0x44), amountIn)
            mstore(add(ptr, 0x64), 0) // min out
            mstore(add(ptr, 0x84), receiver)
            if iszero(
                call(
                    gas(),
                    pool, //
                    0x0,
                    ptr,
                    0xA4,
                    0,
                    0x20
                )
            ) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }

            payFlagAmountOut := mload(0)
            curveData := add(currentOffset, 25)
        }
        return (payFlagAmountOut, curveData);
    }
}
