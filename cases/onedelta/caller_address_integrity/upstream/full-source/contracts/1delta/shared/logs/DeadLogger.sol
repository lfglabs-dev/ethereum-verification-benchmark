// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.28;

/// @notice logs a dead log without any content
abstract contract DeadLogger {
    function _deadLog() internal {
        assembly {
            log0(0x0, 0x0)
        }
    }
}
