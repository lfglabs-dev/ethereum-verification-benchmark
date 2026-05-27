// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

/**
 * This is to check whether the provided parameter is nonempty
 */
library ValidatorLib {
    function _hasData(bytes32 data) internal pure returns (bool hasData) {
        assembly {
            hasData := xor(0, data)
        }
    }

    function _hasAddress(address data) internal pure returns (bool hasData) {
        assembly {
            hasData := xor(0, data)
        }
    }
}
