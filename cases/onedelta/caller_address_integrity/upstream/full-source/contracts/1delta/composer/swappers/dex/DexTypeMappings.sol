// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

library DexTypeMappings {
    /**
     * First Block: Blue Chip DEXs (1)
     */
    uint256 internal constant UNISWAP_V3_ID = 0;
    uint256 internal constant UNISWAP_V2_ID = 1;
    uint256 internal constant UNISWAP_V4_ID = 2;
    uint256 internal constant IZI_ID = 5;
    uint256 internal constant UNISWAP_V2_FOT_ID = 3;

    /**
     * Second Block: Blue Chip DEXs (2): all DEX that behave like curve
     */
    // indexs as input
    // returns out amount
    uint256 internal constant CURVE_V1_STANDARD_ID = 64;
    // curve NG
    uint256 internal constant CURVE_RECEIVED_ID = 65;
    // almost like curve, but slight different implementation,
    // e.g. the function returns no output
    uint256 internal constant CURVE_FORK_ID = 66;

    uint256 internal constant WOO_FI_ID = 80;

    // GMXs (rather rare)
    uint256 internal constant GMX_ID = 90;
    uint256 internal constant KTX_ID = 91;

    /**
     * Third Block: Blue Chips (3): Balancers
     */
    uint256 internal constant BALANCER_V2_ID = 128;
    uint256 internal constant BALANCER_V3_ID = 129;

    // LFM/LFJ LB
    uint256 internal constant LB_ID = 140;

    // more exotics
    uint256 internal constant DODO_ID = 150;
    uint256 internal constant SYNC_SWAP_ID = 160;

    /**
     * Fourth Block: Wrappers
     */
    // wrappers
    uint256 internal constant ERC4626_ID = 253;
    uint256 internal constant ASSET_WRAP_ID = 254;
}
