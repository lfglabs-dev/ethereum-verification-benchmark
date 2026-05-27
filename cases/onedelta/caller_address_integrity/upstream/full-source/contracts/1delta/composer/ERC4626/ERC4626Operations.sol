// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {ERC20Selectors} from "../../shared/selectors/ERC20Selectors.sol";
import {ERC4626Transfers} from "./ERC4626Transfers.sol";
import {ERC4626Ids} from "../enums/DeltaEnums.sol";

/**
 * @notice ERC4626 deposit and withdraw actions
 */
abstract contract ERC4626Operations is ERC4626Transfers {
    /// @notice withdraw from (e.g. morpho) vault
    function _ERC4626Operations(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        uint256 erc4626Operation;
        assembly {
            erc4626Operation := shr(248, calldataload(currentOffset))
            currentOffset := add(currentOffset, 1)
        }
        /**
         * ERC6464 deposit
         */
        if (erc4626Operation == ERC4626Ids.DEPOSIT) {
            currentOffset = _encodeErc4646Deposit(currentOffset);
        }
        /**
         * ERC6464 withdraw
         */
        else if (erc4626Operation == ERC4626Ids.WITHDRAW) {
            currentOffset = _encodeErc4646Withdraw(currentOffset, callerAddress);
        } else {
            _invalidOperation();
        }
        return currentOffset;
    }
}
