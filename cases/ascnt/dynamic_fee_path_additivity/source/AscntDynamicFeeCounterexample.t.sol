// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Phase1FuzzBase} from "./fuzz/Phase1Helpers.sol";

contract AscntDynamicFeeCounterexampleTest is Phase1FuzzBase {
    function test_exact_counterexample_kOne() public view {
        uint24 first = harness.exposedCalculateDynamicFee(1, -1, true, 0, 100, 1_000_000, 1_000_000);
        uint24 second = harness.exposedCalculateDynamicFee(1, -2, true, 0, 100, 1_000_000, 1_000_000);
        uint24 lump = harness.exposedCalculateDynamicFee(2, -1, true, 0, 100, 1_000_000, 1_000_000);

        assertEq(first, 1);
        assertEq(second, 2);
        assertEq(lump, 2);
        assertEq(uint256(first) + uint256(second), 3);
        assertEq(uint256(lump) * 2, 4);
        assertLt(uint256(first) + uint256(second), uint256(lump) * 2);
    }
}
