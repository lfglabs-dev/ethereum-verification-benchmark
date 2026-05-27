// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {Gen2025ActionIds} from "../enums/DeltaEnums.sol";
import {UniswapV4SingletonActions} from "./UniswapV4Singleton.sol";
import {BalancerV3VaultActions} from "./BalancerV3Vault.sol";
import {SharedSingletonActions} from "./Shared.sol";

// solhint-disable max-line-length

/**
 * @notice Everything Uniswap V4 & Balancer V3, the major upgrades for DEXs in 2025
 */
abstract contract Gen2025DexActions is UniswapV4SingletonActions, BalancerV3VaultActions, SharedSingletonActions {
    function _gen2025DexActions(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        uint256 transferOperation;
        assembly {
            let firstSlice := calldataload(currentOffset)
            transferOperation := shr(248, firstSlice)
            currentOffset := add(currentOffset, 1)
        }
        if (transferOperation < Gen2025ActionIds.BAL_V3_TAKE) {
            if (transferOperation == Gen2025ActionIds.UNLOCK) {
                return _singletonUnlock(currentOffset, callerAddress);
            } else if (transferOperation == Gen2025ActionIds.UNI_V4_TAKE) {
                return _unoV4Take(currentOffset);
            } else if (transferOperation == Gen2025ActionIds.UNI_V4_SYNC) {
                return _unoV4Sync(currentOffset);
            } else if (transferOperation == Gen2025ActionIds.UNI_V4_SETTLE) {
                return _unoV4Settle(currentOffset);
            } else {
                _invalidOperation();
            }
        } else {
            if (transferOperation == Gen2025ActionIds.BAL_V3_TAKE) {
                return _encodeBalancerV3Take(currentOffset);
            } else if (transferOperation == Gen2025ActionIds.BAL_V3_SETTLE) {
                return _balancerV3Settle(currentOffset);
            } else {
                _invalidOperation();
            }
        }
    }
}
