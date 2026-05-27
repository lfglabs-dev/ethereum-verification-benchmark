// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

/**
 * Author: Achthar | 1delta
 * /*****************************************************************************
 */
import {DeltaErrors} from "../../../shared/errors/Errors.sol";
import {ERC20Selectors} from "../../../shared/selectors/ERC20Selectors.sol";

/**
 * @title Uniswap V3 type callback implementations
 */
abstract contract V3Callbacker is ERC20Selectors {
    /**
     * This functione executes a simple transfer to shortcut the callback if there is no further calldata
     */
    function clSwapCallback(uint256 amountToPay, address tokenIn, address callerAddress, uint256 calldataLength) internal {
        assembly {
            // one can pass no path to continue
            // we then assume the calldataLength as flag to
            // indicate the pay type
            if lt(calldataLength, 2) {
                let ptr := mload(0x40)

                let success
                // transfer from caller
                switch calldataLength
                case 0 {
                    // selector for transferFrom(address,address,uint256)
                    mstore(ptr, ERC20_TRANSFER_FROM)
                    mstore(add(ptr, 0x04), callerAddress)
                    mstore(add(ptr, 0x24), caller())
                    mstore(add(ptr, 0x44), amountToPay)

                    success := call(gas(), tokenIn, 0, ptr, 0x64, ptr, 32)
                }
                // transfer plain
                default {
                    // selector for transfer(address,uint256)
                    mstore(ptr, ERC20_TRANSFER)
                    mstore(add(ptr, 0x04), caller())
                    mstore(add(ptr, 0x24), amountToPay)
                    success :=
                        call(
                            gas(),
                            tokenIn, // tokenIn, pool + 5x uint8 (i,j,s,a)
                            0,
                            ptr,
                            0x44,
                            ptr,
                            32
                        )
                }

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
                return(0, 0)
            }
        }
        _deltaComposeInternal(
            callerAddress,
            // the naive offset is 132
            // we skip the entire callback validation data
            // that is tokens (+40), fee (+2), caller (+20), forkId (+1) datalength (+2)
            // = 197
            197,
            calldataLength
        );
    }

    function _deltaComposeInternal(address callerAddress, uint256 offset, uint256 length) internal virtual {}
}
