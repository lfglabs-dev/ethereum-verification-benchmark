// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

/**
 * Contract holding the storatge slot for approval management and flash loan gateways
 */
contract Slots {
    /// @notice approve call management slot
    bytes32 internal constant CALL_MANAGEMENT_APPROVALS = 0x1aae13105d9b6581c36534caba5708726e5ea1e03175e823c989a5756966d1f3;

    /// @notice flash loan gateway for Balancer type flash loan
    bytes32 internal constant FLASH_LOAN_GATEWAY_SLOT = 0x9fc772e484014aadda1a3916bdcbf34dd65a99500e92cb6faae6cb2496083ccb;
}
