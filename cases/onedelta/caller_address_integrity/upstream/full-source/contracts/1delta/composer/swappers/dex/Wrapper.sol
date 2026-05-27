// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

// solhint-disable max-line-length

import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../../shared/masks/Masks.sol";

/**
 * @title ERC4626 vault & native wrap "swapper" contract
 * The logic is as follows
 * - the only parameter is an indicator for the operation (0: native wrap | 1: deposit | 2: redeem)
 * - the native case has the direction implied by the asset address (asset=0 mean native),
 *   as such, assetIn=0 means wrap, in this case amountIn=amountOut
 * - ERC4626 only uses deposit and redeem (as these are the exact in operations), these
 *   require the output amount to be read from the returndata
 */
abstract contract Wrapper is ERC20Selectors, Masks {
    /// @dev  deposit(...)
    bytes32 private constant ERC4626_DEPOSIT = 0x6e553f6500000000000000000000000000000000000000000000000000000000;

    /// @dev  redeem(...)
    bytes32 private constant ERC4626_REDEEM = 0xba08765200000000000000000000000000000000000000000000000000000000;

    // NativeTransferFailed()
    bytes4 private constant NATIVE_TRANSFER = 0xf4b3b1bc;

    // WrapFailed()
    bytes4 private constant WRAP = 0xc30d93ce;

    // Note that the for native wrapping, the assetIn/assetOut constellation defines the direction
    // For ERC4626, the direction is defined by the operation parameter
    // 1: deposit: deposit to vault, assetIn is the underlying and assetOut is the vault
    // 2: redeem: redeem shares, assetIn is the vault, assetOut is the underlyinh
    /**
     * This one is for overring the DEX implementation
     * | Offset | Length (bytes) | Description         |
     * |--------|----------------|---------------------|
     * | 0      | 1              | operation           |
     * | 1      | 1              | pay config          | <- 0: caller pays; 1: contract pays; greater: pre-funded
     */
    function _wrapperOperation(
        address assetIn,
        address assetOut,
        uint256 amount,
        address receiver,
        address callerAddress,
        uint256 currentOffset
    )
        internal
        virtual
        returns (uint256 amountOut, uint256 operationThenOffset)
    {
        assembly {
            operationThenOffset := calldataload(currentOffset)
            let ptr := mload(0x40)
            // only need to check whether we have to pull from caller
            // Note: this should be avoided for native in
            if iszero(and(shr(240, operationThenOffset), UINT8_MASK)) {
                // selector for transferFrom(address,address,uint256)
                mstore(ptr, ERC20_TRANSFER_FROM)
                mstore(add(ptr, 0x04), callerAddress)
                mstore(add(ptr, 0x24), address())
                mstore(add(ptr, 0x44), amount)

                let success := call(gas(), assetIn, 0, ptr, 0x64, 0, 32)

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

            // shift operation to lowest byte
            switch shr(248, operationThenOffset)
            case 0 {
                amountOut := amount
                // native is input: wrap
                switch iszero(assetIn)
                case 1 {
                    if iszero(
                        call(
                            gas(),
                            assetOut,
                            amount, // ETH to deposit
                            0x0, // no input
                            0x0, // input size = zero
                            0x0, // output = empty
                            0x0 // output size = zero
                        )
                    ) {
                        // revert when native transfer fails
                        mstore(0, NATIVE_TRANSFER)
                        revert(0, 0x4)
                    }
                    // transfer to destination if needed
                    // this is to make receipts of native consistent with pre-funded
                    // calls
                    if xor(receiver, address()) {
                        // selector for transfer(address,uint256)
                        mstore(ptr, ERC20_TRANSFER)
                        mstore(add(ptr, 0x04), receiver)
                        mstore(add(ptr, 0x24), amount)
                        let success := call(gas(), assetOut, 0, ptr, 0x44, 0, 32)

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
                }
                // assetIn is expected to be wNative
                // note that we do not do a transfer to a receiver as DEXs that require native require
                // to attach native to the respective swap call
                default {
                    // selector for withdraw(uint256)
                    mstore(0x0, 0x2e1a7d4d00000000000000000000000000000000000000000000000000000000)
                    mstore(0x4, amount)
                    if iszero(
                        call(
                            gas(),
                            assetIn,
                            0x0, // no ETH
                            0x0, // start of data
                            0x24, // input size = selector plus amount
                            0x0, // output = empty
                            0x0 // output size = zero
                        )
                    ) {
                        // revert when native transfer fails
                        mstore(0, WRAP)
                        revert(0, 0x4)
                    }

                    // transfer native to receiver if needed
                    if xor(receiver, address()) {
                        if iszero(call(gas(), receiver, amount, 0x0, 0x0, 0x0, 0x0)) {
                            // revert when native transfer fails
                            mstore(0, NATIVE_TRANSFER)
                            revert(0, 0x4)
                        }
                    }
                }
            }
            // the other 2 cases have receiver as parameter
            case 1 {
                // Approve vault if needed
                mstore(0x0, assetIn)
                mstore(0x20, 0x1aae13105d9b6581c36534caba5708726e5ea1e03175e823c989a5756966d1f3) // CALL_MANAGEMENT_APPROVALS
                mstore(0x20, keccak256(0x0, 0x40))
                mstore(0x0, assetOut)
                let key := keccak256(0x0, 0x40)
                // check if already approved
                if iszero(sload(key)) {
                    // selector for approve(address,uint256)
                    mstore(ptr, ERC20_APPROVE)
                    mstore(add(ptr, 0x04), assetOut)
                    mstore(add(ptr, 0x24), MAX_UINT256)
                    pop(call(gas(), assetIn, 0, ptr, 0x44, ptr, 32))
                    sstore(key, 1)
                }

                mstore(ptr, ERC4626_DEPOSIT)
                mstore(add(ptr, 0x4), amount) // assets
                mstore(add(ptr, 0x24), receiver) // receiver

                if iszero(call(gas(), assetOut, 0x0, ptr, 0x44, 0x0, 0x20)) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0x0, returndatasize())
                }
                amountOut := mload(0)
            }
            default {
                // this one should not need an approve
                mstore(ptr, ERC4626_REDEEM)
                mstore(add(ptr, 0x4), amount) // shares
                mstore(add(ptr, 0x24), receiver) // receiver
                mstore(add(ptr, 0x44), address()) // owner is self as we expect to hold the vault shares

                if iszero(call(gas(), assetIn, 0x0, ptr, 0x64, 0x0, 0x20)) {
                    returndatacopy(0, 0, returndatasize())
                    revert(0x0, returndatasize())
                }
                amountOut := mload(0)
            }
            operationThenOffset := add(currentOffset, 2)
        }
        return (amountOut, operationThenOffset);
    }
}
