// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {Slots} from "../../../../slots/Slots.sol";
import {Masks} from "../../../../../shared/masks/Masks.sol";
import {DeltaErrors} from "../../../../../shared/errors/Errors.sol";

/**
 * Flash loaning through BalancerV2
 */
contract BalancerV2FlashLoanCallback is Slots, Masks, DeltaErrors {
    // Balancer V2 vaults
    address private constant BALANCER_V2 = 0xBA12222222228d8Ba445958a75a0704d566BF2C8;
    address private constant SWAAP = 0xd315a9C38eC871068FEC378E4Ce78AF528C76293;

    /**
     * @dev Balancer flash loan call
     * Gated via flash loan gateway flag to prevent calls from sources other than this contract
     */
    function receiveFlashLoan(
        address[] calldata,
        uint256[] calldata,
        uint256[] calldata,
        bytes calldata params //
    )
        external
    {
        address origCaller;
        uint256 calldataOffset;
        uint256 calldataLength;
        assembly {
            calldataOffset := params.offset

            // validate caller via provided poolId
            let firstWord := calldataload(calldataOffset)

            // Validate the caller
            // We check that the caller is one of the lending pools
            // This is a crucial check since this makes
            // the initiator paramter the caller of flashLoan
            let pool
            switch and(UINT8_MASK, shr(88, firstWord))
            case 0 { pool := BALANCER_V2 }
            case 2 { pool := SWAAP }
            // We revert on any other id
            default {
                mstore(0, INVALID_FLASH_LOAN)
                revert(0, 0x4)
            }
            // revert if caller is not a whitelisted pool
            if xor(caller(), pool) {
                mstore(0, INVALID_CALLER)
                revert(0, 0x4)
            }

            // check that the flag is set correctly
            if iszero(eq(1, tload(FLASH_LOAN_GATEWAY_SLOT))) {
                mstore(0, INVALID_CALLER)
                revert(0, 0x4)
            }

            // Close the gateway slot afterwards!
            // This prevents a double entry though 2 acccepted
            // Balancer V2 forks where one would use the first
            // through this contract, pass the validation, then use the second to
            // reenter from an attacker contract - the gateway would then be open
            // and the attacker could execute an arbitrary delta compose.
            // Locking the callback again here (instead of after the flashLoan call)
            // prevents this scenario!
            tstore(FLASH_LOAN_GATEWAY_SLOT, 0)
            // Get the original caller from the beginnig of the calldata
            // From here on we have validated that the origCaller
            // was attached in the deltaCompose function
            // Otherwise, this would be a vulnerability
            origCaller := shr(96, firstWord)
            // shift / slice params
            calldataOffset := add(calldataOffset, 21)
            calldataLength := sub(params.length, 21)
        }
        // within the flash loan, any compose operation
        // can be executed
        _deltaComposeInternal(origCaller, calldataOffset, calldataLength);
    }

    function _deltaComposeInternal(address callerAddress, uint256 offset, uint256 length) internal virtual {}
}
