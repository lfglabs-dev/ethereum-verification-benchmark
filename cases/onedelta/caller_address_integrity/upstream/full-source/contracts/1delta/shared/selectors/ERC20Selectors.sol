// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

abstract contract ERC20Selectors {
    ////////////////////////////////////////////////////
    // ERC20 selectors
    ////////////////////////////////////////////////////

    /// @dev selector for approve(address,uint256)
    bytes32 internal constant ERC20_APPROVE = 0x095ea7b300000000000000000000000000000000000000000000000000000000;

    /// @dev selector for transferFrom(address,address,uint256)
    bytes32 internal constant ERC20_TRANSFER_FROM = 0x23b872dd00000000000000000000000000000000000000000000000000000000;

    /// @dev selector for transfer(address,uint256)
    bytes32 internal constant ERC20_TRANSFER = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;

    /// @dev selector for allowance(address,address)
    bytes32 internal constant ERC20_ALLOWANCE = 0xdd62ed3e00000000000000000000000000000000000000000000000000000000;

    /// @dev selector for balanceOf(address)
    bytes32 internal constant ERC20_BALANCE_OF = 0x70a0823100000000000000000000000000000000000000000000000000000000;
}
