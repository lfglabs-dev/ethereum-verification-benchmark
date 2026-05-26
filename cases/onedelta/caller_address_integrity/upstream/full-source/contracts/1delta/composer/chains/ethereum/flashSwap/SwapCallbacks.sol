// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {UniV4Callbacks} from "./callbacks/UniV4Callback.sol";
import {UniV3Callbacks, V3Callbacker} from "./callbacks/UniV3Callback.sol";
import {UniV2Callbacks} from "./callbacks/UniV2Callback.sol";
import {DodoV2Callbacks} from "./callbacks/DodoV2Callback.sol";
import {BalancerV3Callbacks} from "./callbacks/BalancerV3Callback.sol";

/**
 * @title Swap Callback executor
 * @author 1delta Labs AG
 */
contract SwapCallbacks is
    UniV4Callbacks,
    UniV3Callbacks,
    UniV2Callbacks,
    DodoV2Callbacks,
    BalancerV3Callbacks //
{
    // override the compose
    function _deltaComposeInternal(
        address callerAddress,
        uint256 offset,
        uint256 length
    )
        internal
        virtual
        override(
            UniV4Callbacks,
            V3Callbacker,
            UniV2Callbacks,
            DodoV2Callbacks,
            BalancerV3Callbacks //
        )
    {}

    /**
     * Swap callbacks are taken in the fallback
     * We do this to have an easier time in validating similar callbacks
     * with separate selectors
     *
     * We identify the selector in the fallback and then map it to the DEX
     *
     * Note that each "_execute..." function returns (exits) when a callback is run.
     *
     * If it falls through all variations, it reverts at the end.
     */
    fallback() external {
        bytes32 selector;
        assembly {
            selector :=
                and(
                    0xffffffff00000000000000000000000000000000000000000000000000000000, // masks upper 4 bytes
                    calldataload(0)
                )
        }
        _executeUniV3IfSelector(selector);
        _executeUniV2IfSelector(selector);
        _executeDodoV2IfSelector(selector);

        // we do not allow a fallthrough
        assembly {
            revert(0, 0)
        }
    }
}
