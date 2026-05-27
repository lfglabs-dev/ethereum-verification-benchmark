// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {BaseUtils} from "contracts/1delta/composer/generic/BaseUtils.sol";

/**
 * @title Token transfer contract - should work across all EVMs - use Uniswap style Permit2
 */
contract AssetTransfers is BaseUtils {
    // approval slot
    bytes32 private constant CALL_MANAGEMENT_APPROVALS = 0x1aae13105d9b6581c36534caba5708726e5ea1e03175e823c989a5756966d1f3;

    /// @notice fixed selector transferFrom(...) on permit2
    bytes32 private constant PERMIT2_TRANSFER_FROM = 0x36c7851600000000000000000000000000000000000000000000000000000000;

    /// @notice deterministically deployed pemrit2 address
    address private constant PERMIT2 = 0x000000000022D473030F116dDEE9F6B43aC78BA3;

    /*
     * | Offset | Length (bytes) | Description         |
     * |--------|----------------|---------------------|
     * | 0      | 20             | asset               |
     * | 20     | 20             | receiver            |
     * | 40     | 16             | amount              |
     */
    function _permit2TransferFrom(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        ////////////////////////////////////////////////////
        // Transfers tokens from caller to this address
        // zero amount flags that the entire balance is sent
        ////////////////////////////////////////////////////
        assembly {
            let underlying := shr(96, calldataload(currentOffset))
            let receiver := shr(96, calldataload(add(currentOffset, 20)))
            let amount := shr(128, calldataload(add(currentOffset, 40)))

            // when entering 0 as amount, use the callwe balance
            if iszero(amount) {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add this address as parameter
                mstore(0x04, callerAddress)
                // call to token
                pop(
                    staticcall(
                        gas(),
                        underlying, // token
                        0x0,
                        0x24,
                        0x0,
                        0x20
                    )
                )
                // load the retrieved balance
                amount := mload(0x0)
            }

            let ptr := mload(0x40)
            mstore(ptr, PERMIT2_TRANSFER_FROM)
            mstore(add(ptr, 0x04), callerAddress)
            mstore(add(ptr, 0x24), receiver)
            mstore(add(ptr, 0x44), amount)
            mstore(add(ptr, 0x64), underlying)
            if iszero(call(gas(), PERMIT2, 0, ptr, 0x84, 0x0, 0x0)) {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
            currentOffset := add(currentOffset, 56)
        }
        return currentOffset;
    }

    /*
     * | Offset | Length (bytes) | Description         |
     * |--------|----------------|---------------------|
     * | 0      | 20             | asset               |
     * | 20     | 20             | receiver            |
     * | 40     | 16             | amount              |
     */
    function _transferFrom(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        ////////////////////////////////////////////////////
        // Transfers tokens from caller to this address
        // zero amount flags that the entire balance is sent
        ////////////////////////////////////////////////////
        assembly {
            let underlying := shr(96, calldataload(currentOffset))
            let receiver := shr(96, calldataload(add(currentOffset, 20)))
            let amount := shr(128, calldataload(add(currentOffset, 40)))

            // when entering 0 as amount, use the callwe balance
            if iszero(amount) {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add this address as parameter
                mstore(0x04, callerAddress)
                // call to token
                pop(
                    staticcall(
                        gas(),
                        underlying, // token
                        0x0,
                        0x24,
                        0x0,
                        0x20
                    )
                )
                // load the retrieved balance
                amount := mload(0x0)
            }

            let ptr := mload(0x40) // free memory pointer

            // selector for transferFrom(address,address,uint256)
            mstore(ptr, ERC20_TRANSFER_FROM)
            mstore(add(ptr, 0x04), callerAddress)
            mstore(add(ptr, 0x24), receiver)
            mstore(add(ptr, 0x44), amount)

            let success := call(gas(), underlying, 0, ptr, 0x64, ptr, 32)

            let rdsize := returndatasize()

            if iszero(
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
            ) {
                returndatacopy(0, 0, rdsize)
                revert(0, rdsize)
            }
            currentOffset := add(currentOffset, 56)
        }
        return currentOffset;
    }

    /*
     * | Offset | Length (bytes) | Description         |
     * |--------|----------------|---------------------|
     * | 0      | 20             | asset               |
     * | 20     | 20             | receiver            | <- use wrapped native here to wrap
     * | 40     | 1              | config              |
     * | 41     | 16             | amount              |
     */
    function _sweep(uint256 currentOffset) internal returns (uint256) {
        ////////////////////////////////////////////////////
        // Transfers either token or native balance from this
        // contract to receiver. Reverts if minAmount is
        // less than the contract balance
        //  config
        //  0: sweep balance and validate against amount
        //     fetches the balance and checks balance >= amount
        //  1: transfer amount to receiver, skip validation
        ////////////////////////////////////////////////////
        assembly {
            let underlying := shr(96, calldataload(currentOffset))
            // we skip shr by loading the address to the lower bytes
            let receiver := shr(96, calldataload(add(currentOffset, 20)))
            // load so that amount is in the lower 14 bytes already
            let providedAmount := calldataload(add(currentOffset, 25))
            // load config
            let config := and(UINT8_MASK, shr(128, providedAmount))
            // mask amount
            providedAmount := and(UINT128_MASK, providedAmount)

            // initialize transferAmount
            let transferAmount

            // zero address is native
            switch iszero(underlying)
            ////////////////////////////////////////////////////
            // Transfer token
            ////////////////////////////////////////////////////
            case 0 {
                // for config = 0, the amount is the balance and we
                // check that the balance is larger tha the amount provided
                switch config
                case 0 {
                    // selector for balanceOf(address)
                    mstore(0, ERC20_BALANCE_OF)
                    // add this address as parameter
                    mstore(0x04, address())
                    // call to token
                    pop(
                        staticcall(
                            gas(),
                            underlying,
                            0x0,
                            0x24,
                            0x0,
                            0x20 //
                        )
                    )
                    // load the retrieved balance
                    transferAmount := mload(0x0)
                    // revert if balance is not enough
                    if lt(transferAmount, providedAmount) {
                        mstore(0, SLIPPAGE)
                        revert(0, 0x4)
                    }
                }
                default { transferAmount := providedAmount }

                if gt(transferAmount, 0) {
                    let ptr := mload(0x40) // free memory pointer

                    // selector for transfer(address,uint256)
                    mstore(ptr, ERC20_TRANSFER)
                    mstore(add(ptr, 0x04), receiver)
                    mstore(add(ptr, 0x24), transferAmount)

                    let success := call(gas(), underlying, 0, ptr, 0x44, ptr, 32)

                    let rdsize := returndatasize()

                    if iszero(
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
                    ) {
                        returndatacopy(0, 0, rdsize)
                        revert(0, rdsize)
                    }
                }
            }
            ////////////////////////////////////////////////////
            // Transfer native
            ////////////////////////////////////////////////////
            default {
                switch config
                case 0 {
                    transferAmount := selfbalance()
                    // revert if balance is not enough
                    if lt(transferAmount, providedAmount) {
                        mstore(0, SLIPPAGE)
                        revert(0, 0x4)
                    }
                }
                default { transferAmount := providedAmount }

                if gt(transferAmount, 0) {
                    if iszero(
                        call(
                            gas(),
                            receiver,
                            transferAmount,
                            0x0, // input = empty for fallback/receive
                            0x0, // input size = zero
                            0x0, // output = empty
                            0x0 // output size = zero
                        )
                    ) {
                        mstore(0, NATIVE_TRANSFER)
                        revert(0, 0x4) // revert when native transfer fails
                    }
                }
            }
            currentOffset := add(currentOffset, 57)
        }
        return currentOffset;
    }

    /*
     * | Offset | Length (bytes) | Description          |
     * |--------|----------------|----------------------|
     * | 0      | 20             | token                |
     * | 20     | 20             | target               |
     */
    function _approve(uint256 currentOffset) internal returns (uint256) {
        assembly {
            // load underlying and target
            let underlying := shr(96, calldataload(currentOffset))
            let target := shr(96, calldataload(add(currentOffset, 20)))
            // check whether the approval alderady was done
            // if so, we can skip this part silently
            mstore(0x0, underlying)
            mstore(0x20, CALL_MANAGEMENT_APPROVALS)
            mstore(0x20, keccak256(0x0, 0x40))
            mstore(0x0, target)
            let key := keccak256(0x0, 0x40)
            // check if already approved
            if iszero(sload(key)) {
                let ptr := mload(0x40)
                // selector for approve(address,uint256)
                mstore(ptr, ERC20_APPROVE)
                mstore(add(ptr, 0x04), target)
                mstore(add(ptr, 0x24), MAX_UINT256)
                pop(
                    call(
                        gas(),
                        underlying, //
                        0,
                        ptr,
                        0x44,
                        ptr,
                        32
                    )
                )
                sstore(key, 1)
            }
            currentOffset := add(currentOffset, 40)
        }
        return currentOffset;
    }

    /*
     * | Offset | Length (bytes) | Description         |
     * |--------|----------------|---------------------|
     * | 0      | 20             | wrappedNativeAddress|
     * | 20     | 20             | receiver            |
     * | 40     | 1              | config              |
     * | 41     | 16             | amount              |
     */
    function _unwrap(uint256 currentOffset) internal virtual returns (uint256) {
        ////////////////////////////////////////////////////
        // Transfers either token or native balance from this
        // contract to receiver. Reverts if minAmount is
        // less than the contract balance
        //  config
        //  0: sweep balance and validate against amount
        //     fetches the balance and checks balance >= amount
        //  1: transfer amount to receiver, skip validation
        ////////////////////////////////////////////////////
        assembly {
            // load receiver
            let wrapperAsset := shr(96, calldataload(currentOffset))
            // load receiver
            let receiver := shr(96, calldataload(add(currentOffset, 20)))
            // load so that amount is in the lower 14 bytes already
            let providedAmount := calldataload(add(currentOffset, 25))
            // load config
            let config := and(UINT8_MASK, shr(128, providedAmount))
            // mask amount
            providedAmount := and(UINT128_MASK, providedAmount)

            let transferAmount

            // mask away the top bitmap
            providedAmount := and(UINT120_MASK, providedAmount)
            // validate if config is zero, otherwise skip
            switch config
            case 0 {
                // selector for balanceOf(address)
                mstore(0x0, ERC20_BALANCE_OF)
                // add this address as parameter
                mstore(0x4, address())

                // call to underlying
                pop(staticcall(gas(), wrapperAsset, 0x0, 0x24, 0x0, 0x20))

                transferAmount := mload(0x0)
                if lt(transferAmount, providedAmount) {
                    mstore(0, SLIPPAGE)
                    revert(0, 0x4)
                }
            }
            default { transferAmount := providedAmount }

            if gt(transferAmount, 0) {
                // selector for withdraw(uint256)
                mstore(0x0, 0x2e1a7d4d00000000000000000000000000000000000000000000000000000000)
                mstore(0x4, transferAmount)
                if iszero(
                    call(
                        gas(),
                        wrapperAsset,
                        0x0, // no ETH
                        0x0, // start of data
                        0x24, // input size = selector plus amount
                        0x0, // output = empty
                        0x0 // output size = zero
                    )
                ) {
                    // should only revert if receiver cannot receive native
                    mstore(0, NATIVE_TRANSFER)
                    revert(0, 0x4)
                }
                // transfer to receiver if different from this address
                if xor(receiver, address()) {
                    // transfer native to receiver
                    if iszero(
                        call(
                            gas(),
                            receiver,
                            transferAmount,
                            0x0, // input = empty for fallback
                            0x0, // input size = zero
                            0x0, // output = empty
                            0x0 // output size = zero
                        )
                    ) {
                        // should only revert if receiver cannot receive native
                        mstore(0, NATIVE_TRANSFER)
                        revert(0, 0x4)
                    }
                }
            }
            currentOffset := add(currentOffset, 57)
        }
        return currentOffset;
    }
}
