// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {PermitUtils} from "../../shared/permit/PermitUtils.sol";
import {Masks} from "../../shared/masks/Masks.sol";
import {DeltaErrors} from "../../shared/errors/Errors.sol";
import {PermitIds} from "../enums/DeltaEnums.sol";

abstract contract Permits is Masks, PermitUtils, DeltaErrors {
    /*
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 1              | permitOperation                 |
     * | 1      | 20             | asset                           |
     * | 21     | 2              | permitLength                    |
     * | 23     | permitLength   | data                            |
     */
    function _permit(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        uint256 permitOperation;
        address permitTarget;
        uint256 permitLength;
        uint256 permitOffset;
        assembly {
            let firstSlice := calldataload(currentOffset)
            permitOperation := shr(248, firstSlice)
            // this can be a token or morpho blue or compound V3 comet
            permitTarget := and(ADDRESS_MASK, shr(88, firstSlice))
            // calldata length
            permitLength := and(UINT16_MASK, shr(72, firstSlice))
            // increment offset
            permitOffset := add(currentOffset, 23)
            // increment offset
            currentOffset := add(permitOffset, permitLength)
        }
        if (permitOperation == PermitIds.TOKEN_PERMIT) {
            _tryPermit(permitTarget, permitOffset, permitLength, callerAddress);
            return currentOffset;
        } else if (permitOperation == PermitIds.AAVE_V3_CREDIT_PERMIT) {
            _tryCreditPermit(permitTarget, permitOffset, permitLength, callerAddress);
            return currentOffset;
        } else if (permitOperation == PermitIds.ALLOW_CREDIT_PERMIT) {
            _tryFlagBasedLendingPermit(permitTarget, permitOffset, permitLength, callerAddress);
            return currentOffset;
        } else {
            _invalidOperation();
        }
    }
}
