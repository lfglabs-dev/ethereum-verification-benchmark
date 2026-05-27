// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {Masks} from "../../../../../shared/masks/Masks.sol";
import {DeltaErrors} from "../../../../../shared/errors/Errors.sol";

/**
 * @title All Moolah flash callbacks
 */
contract MoolahFlashLoanCallback is Masks, DeltaErrors {
    /// @dev Constant Moolah address
    address private constant LISTA_DAO = 0xf820fB4680712CD7263a0D3D024D5b5aEA82Fd70;

    /**
     * Moolah callbacks
     */

    /// @dev Moolah flash loan
    function onMoolahFlashLoan(uint256, bytes calldata) external {
        _onMoolahCallback();
    }

    /// @dev Moolah supply callback
    function onMoolahSupply(uint256, bytes calldata) external {
        _onMoolahCallback();
    }

    /// @dev Moolah repay callback
    function onMoolahRepay(uint256, bytes calldata) external {
        _onMoolahCallback();
    }

    /// @dev Moolah supply collateral callback
    function onMoolahSupplyCollateral(uint256, bytes calldata) external {
        _onMoolahCallback();
    }

    /// @dev Moolah flash loans are callbacks to msg.sender,
    /// Since it is universal batching and the same validation for all
    /// Moolah callbacks, we can use the same logic everywhere
    function _onMoolahCallback() internal {
        address origCaller;
        uint256 calldataLength;
        assembly {
            // validate caller
            // - extract id from params
            let firstWord := calldataload(100)

            switch and(UINT8_MASK, shr(88, firstWord))
            case 0 {
                if xor(caller(), LISTA_DAO) {
                    mstore(0, INVALID_CALLER)
                    revert(0, 0x4)
                }
            }
            default {
                mstore(0, INVALID_FLASH_LOAN)
                revert(0, 0x4)
            }
            // Slice the original caller off the beginnig of the calldata
            // From here on we have validated that the origCaller
            // was attached in the deltaCompose function
            // Otherwise, this would be a vulnerability
            origCaller := shr(96, firstWord)
            // shift / slice params
            calldataLength := sub(calldataload(68), 21)
        }
        // within the flash loan, any compose operation
        // can be executed
        _deltaComposeInternal(
            origCaller,
            121, // offset is constant (100 native + 21)
            calldataLength
        );
    }

    function _deltaComposeInternal(address callerAddress, uint256 offset, uint256 length) internal virtual {}
}
