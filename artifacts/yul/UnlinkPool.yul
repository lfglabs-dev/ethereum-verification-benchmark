object "UnlinkPool" {
    code {
        if callvalue() {
            revert(0, 0)
        }
        function mappingSlot(baseSlot, key) -> slot {
            mstore(0, key)
            mstore(32, baseSlot)
            slot := keccak256(0, 64)
        }
        function __verity_array_element_calldata_checked(data_offset, length, index) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            word := calldataload(add(data_offset, mul(index, 32)))
        }
        function __verity_array_element_memory_checked(data_offset, length, index) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            word := mload(add(data_offset, mul(index, 32)))
        }
        function __verity_array_element_word_calldata_checked(data_offset, length, index, element_words, word_offset) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            word := calldataload(add(data_offset, mul(add(mul(index, element_words), word_offset), 32)))
        }
        function __verity_array_element_word_memory_checked(data_offset, length, index, element_words, word_offset) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            word := mload(add(data_offset, mul(add(mul(index, element_words), word_offset), 32)))
        }
        function __verity_array_element_dynamic_word_calldata_checked(data_offset, length, index, word_offset) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_word_pos := add(add(data_offset, __element_rel_offset), mul(word_offset, 32))
            if gt(__element_word_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := calldataload(__element_word_pos)
        }
        function __verity_array_element_dynamic_word_memory_checked(data_offset, length, index, word_offset) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_word_pos := add(add(data_offset, __element_rel_offset), mul(word_offset, 32))
            word := mload(__element_word_pos)
        }
        function __verity_array_element_dynamic_data_offset_calldata_checked(data_offset, length, index) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_head_pos := add(data_offset, __element_rel_offset)
            if gt(__element_head_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := __element_head_pos
        }
        function __verity_array_element_dynamic_data_offset_memory_checked(data_offset, length, index) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_head_pos := add(data_offset, __element_rel_offset)
            word := __element_head_pos
        }
        function __verity_array_element_dynamic_member_length_calldata_checked(data_offset, length, index, word_offset) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_head_pos := add(data_offset, __element_rel_offset)
            let __member_rel_offset := calldataload(add(__element_head_pos, mul(word_offset, 32)))
            let __member_data_pos := add(__element_head_pos, __member_rel_offset)
            if gt(__member_data_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := calldataload(__member_data_pos)
        }
        function __verity_array_element_dynamic_member_length_memory_checked(data_offset, length, index, word_offset) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_head_pos := add(data_offset, __element_rel_offset)
            let __member_rel_offset := mload(add(__element_head_pos, mul(word_offset, 32)))
            let __member_data_pos := add(__element_head_pos, __member_rel_offset)
            word := mload(__member_data_pos)
        }
        function __verity_array_element_dynamic_member_data_offset_calldata_checked(data_offset, length, index, word_offset) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_head_pos := add(data_offset, __element_rel_offset)
            let __member_rel_offset := calldataload(add(__element_head_pos, mul(word_offset, 32)))
            let __member_data_pos := add(__element_head_pos, __member_rel_offset)
            if gt(__member_data_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := add(__member_data_pos, 32)
        }
        function __verity_array_element_dynamic_member_data_offset_memory_checked(data_offset, length, index, word_offset) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_head_pos := add(data_offset, __element_rel_offset)
            let __member_rel_offset := mload(add(__element_head_pos, mul(word_offset, 32)))
            let __member_data_pos := add(__element_head_pos, __member_rel_offset)
            word := add(__member_data_pos, 32)
        }
        function __verity_array_element_dynamic_member_element_calldata_checked(data_offset, length, index, word_offset, inner_index) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_head_pos := add(data_offset, __element_rel_offset)
            let __member_rel_offset := calldataload(add(__element_head_pos, mul(word_offset, 32)))
            let __member_data_pos := add(__element_head_pos, __member_rel_offset)
            let __member_length := calldataload(__member_data_pos)
            if iszero(lt(inner_index, __member_length)) {
                revert(0, 0)
            }
            let __word_pos := add(__member_data_pos, add(32, mul(inner_index, 32)))
            if gt(__word_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := calldataload(__word_pos)
        }
        function __verity_array_element_dynamic_member_element_memory_checked(data_offset, length, index, word_offset, inner_index) -> word {
            if iszero(lt(index, length)) {
                revert(0, 0)
            }
            let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
            if lt(__element_rel_offset, mul(length, 32)) {
                revert(0, 0)
            }
            let __element_head_pos := add(data_offset, __element_rel_offset)
            let __member_rel_offset := mload(add(__element_head_pos, mul(word_offset, 32)))
            let __member_data_pos := add(__element_head_pos, __member_rel_offset)
            let __member_length := mload(__member_data_pos)
            if iszero(lt(inner_index, __member_length)) {
                revert(0, 0)
            }
            let __word_pos := add(__member_data_pos, add(32, mul(inner_index, 32)))
            word := mload(__word_pos)
        }
        function __verity_param_dynamic_head_word_calldata_checked(data_offset, word_offset) -> word {
            let __head_word_pos := add(data_offset, mul(word_offset, 32))
            if gt(__head_word_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := calldataload(__head_word_pos)
        }
        function __verity_param_dynamic_head_word_memory_checked(data_offset, word_offset) -> word {
            let __head_word_pos := add(data_offset, mul(word_offset, 32))
            word := mload(__head_word_pos)
        }
        function __verity_param_dynamic_member_length_calldata_checked(data_offset, word_offset) -> word {
            let __member_rel_offset := calldataload(add(data_offset, mul(word_offset, 32)))
            let __member_data_pos := add(data_offset, __member_rel_offset)
            if gt(__member_data_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := calldataload(__member_data_pos)
        }
        function __verity_param_dynamic_member_length_memory_checked(data_offset, word_offset) -> word {
            let __member_rel_offset := mload(add(data_offset, mul(word_offset, 32)))
            let __member_data_pos := add(data_offset, __member_rel_offset)
            word := mload(__member_data_pos)
        }
        function __verity_param_dynamic_member_data_offset_calldata_checked(data_offset, word_offset) -> word {
            let __member_rel_offset := calldataload(add(data_offset, mul(word_offset, 32)))
            let __member_data_pos := add(data_offset, __member_rel_offset)
            if gt(__member_data_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := add(__member_data_pos, 32)
        }
        function __verity_param_dynamic_member_data_offset_memory_checked(data_offset, word_offset) -> word {
            let __member_rel_offset := mload(add(data_offset, mul(word_offset, 32)))
            let __member_data_pos := add(data_offset, __member_rel_offset)
            word := add(__member_data_pos, 32)
        }
        function __verity_param_dynamic_member_element_calldata_checked(data_offset, word_offset, inner_index) -> word {
            let __member_rel_offset := calldataload(add(data_offset, mul(word_offset, 32)))
            let __member_data_pos := add(data_offset, __member_rel_offset)
            let __member_length := calldataload(__member_data_pos)
            if iszero(lt(inner_index, __member_length)) {
                revert(0, 0)
            }
            let __word_pos := add(__member_data_pos, add(32, mul(inner_index, 32)))
            if gt(__word_pos, sub(calldatasize(), 32)) {
                revert(0, 0)
            }
            word := calldataload(__word_pos)
        }
        function __verity_param_dynamic_member_element_memory_checked(data_offset, word_offset, inner_index) -> word {
            let __member_rel_offset := mload(add(data_offset, mul(word_offset, 32)))
            let __member_data_pos := add(data_offset, __member_rel_offset)
            let __member_length := mload(__member_data_pos)
            if iszero(lt(inner_index, __member_length)) {
                revert(0, 0)
            }
            let __word_pos := add(__member_data_pos, add(32, mul(inner_index, 32)))
            word := mload(__word_pos)
        }
        function internal_internal_initialize(verifierRouter, ownerAddr, relayer) {
            if iszero(eq(sload(0), 0)) {
                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(4, 32)
                mstore(36, 23)
                mstore(68, 0x696e697469616c697a657220616c72656164792072756e000000000000000000)
                revert(0, 100)
            }
            sstore(0, 1)
            let qMinusG1Y := 21888242871839275222246405745257275088696311157297823662689037894645226208581
            let g2x1 := 11559732032986387107991004021392285783925812861821192530917403151452391805634
            let g2x2 := 10857046999023057135944570762232829481370756359578518086990519993285655852781
            let g2y1 := 4082367875863433681332203403145435568316851327593401208105741076214120093531
            let g2y2 := 8495653923123431417604973247489272438418190587263600148770280649306958101930
            mstore(0, 1)
            mstore(32, 2)
            mstore(64, g2x1)
            mstore(96, g2x2)
            mstore(128, g2y1)
            mstore(160, g2y2)
            mstore(192, 1)
            mstore(224, qMinusG1Y)
            mstore(256, g2x1)
            mstore(288, g2x2)
            mstore(320, g2y1)
            mstore(352, g2y2)
            let pairA := 0
            {
                let __bn256_pairing_output_offset := 0
                let __bn256_pairing_success := staticcall(gas(), 8, 0, 384, __bn256_pairing_output_offset, 32)
                if iszero(__bn256_pairing_success) {
                    revert(0, 0)
                }
                pairA := mload(__bn256_pairing_output_offset)
            }
            if iszero(eq(pairA, 1)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            mstore(0, 1)
            mstore(32, 2)
            let pairB := 0
            {
                let __bn256_pairing_output_offset := 0
                let __bn256_pairing_success := staticcall(gas(), 8, 0, 192, __bn256_pairing_output_offset, 32)
                if iszero(__bn256_pairing_success) {
                    revert(0, 0)
                }
                pairB := mload(__bn256_pairing_output_offset)
            }
            if iszero(eq(pairB, 0)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let twoG1x := 1368015179489954701390400359078579693043519447331113978918064868415326638035
            let twoG1y := 9918110051302171585080402603319702774565515993150576347155970296011118125764
            let mul2x := 0
            let mul2y := 0
            {
                mstore(0, 1)
                mstore(32, 2)
                mstore(64, 2)
                let __bn256_mul_success := staticcall(gas(), 7, 0, 96, 0, 64)
                if iszero(__bn256_mul_success) {
                    revert(0, 0)
                }
                mul2x := mload(0)
                mul2y := mload(32)
            }
            if iszero(eq(mul2x, twoG1x)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(eq(mul2y, twoG1y)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let mul3x := 0
            let mul3y := 0
            {
                mstore(0, 1)
                mstore(32, 2)
                mstore(64, 3)
                let __bn256_mul_success := staticcall(gas(), 7, 0, 96, 0, 64)
                if iszero(__bn256_mul_success) {
                    revert(0, 0)
                }
                mul3x := mload(0)
                mul3y := mload(32)
            }
            if iszero(or(iszero(iszero(iszero(eq(mul3x, twoG1x)))), iszero(iszero(iszero(eq(mul3y, twoG1y)))))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let add2x := 0
            let add2y := 0
            {
                mstore(0, 1)
                mstore(32, 2)
                mstore(64, 1)
                mstore(96, 2)
                let __bn256_add_success := staticcall(gas(), 6, 0, 128, 0, 64)
                if iszero(__bn256_add_success) {
                    revert(0, 0)
                }
                add2x := mload(0)
                add2y := mload(32)
            }
            if iszero(eq(add2x, twoG1x)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(eq(add2y, twoG1y)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let add3x := 0
            let add3y := 0
            {
                mstore(0, 1)
                mstore(32, 2)
                mstore(64, twoG1x)
                mstore(96, twoG1y)
                let __bn256_add_success := staticcall(gas(), 6, 0, 128, 0, 64)
                if iszero(__bn256_add_success) {
                    revert(0, 0)
                }
                add3x := mload(0)
                add3y := mload(32)
            }
            if iszero(or(iszero(iszero(iszero(eq(add3x, twoG1x)))), iszero(iszero(iszero(eq(add3y, twoG1y)))))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(eq(mul3x, add3x)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(eq(mul3y, add3y)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                    let __err_hash := keccak256(__err_ptr, 27)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            sstore(1, and(ownerAddr, 0xffffffffffffffffffffffffffffffffffffffff))
            sstore(2, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
            if iszero(iszero(eq(verifierRouter, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 19)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            sstore(97642014805756523509931909943000448576722218578626833372473198353469753044997, and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
            if iszero(iszero(eq(relayer, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 19)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let already := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
            if iszero(eq(already, 0)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c52656c61796572416c72656164794163746976652829000000000000)
                    let __err_hash := keccak256(__err_ptr, 26)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 1)
            {
                let __evt_ptr := mload(64)
                mstore(add(__evt_ptr, 0), 0x52656c6179657241646465642861646472657373290000000000000000000000)
                let __evt_topic0 := keccak256(__evt_ptr, 21)
                log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
            }
            stop()
        }
        function internal_internal_authorizeUpgrade(_newImplementation) {
            if iszero(eq(caller(), sload(1))) {
                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(4, 32)
                mstore(36, 38)
                mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                revert(0, 132)
            }
            stop()
        }
        function internal_internal_renounceOwnership() {
            if iszero(eq(caller(), sload(1))) {
                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(4, 32)
                mstore(36, 38)
                mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                revert(0, 132)
            }
            {
                let __err_ptr := mload(64)
                mstore(add(__err_ptr, 0), 0x506f6f6c52656e6f756e63654f776e65727368697044697361626c6564282900)
                let __err_hash := keccak256(__err_ptr, 31)
                let __err_selector := shl(224, shr(224, __err_hash))
                mstore(0, __err_selector)
                let __err_tail := 0
                revert(0, add(4, __err_tail))
            }
            stop()
        }
        function internal_internal_isRelayer(account) -> __ret0 {
            let r := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, account))
            __ret0 := r
            leave
        }
        function internal_internal_nextLeafIndex() -> __ret0 {
            let n := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
            __ret0 := n
            leave
        }
        function internal_internal_hashNote(npk, _token, amount) -> __ret0 {
            __ret0 := poseidonT4(npk, _token, amount)
            leave
        }
        function internal_internal_poseidon2(lhs, rhs) -> __ret0 {
            __ret0 := poseidonT3(lhs, rhs)
            leave
        }
        function internal_internal_validateNoteFields(npk, token, amount) {
            if iszero(iszero(eq(token, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465546f6b656e282900000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 22)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(and(iszero(iszero(iszero(eq(amount, 0)))), iszero(iszero(iszero(gt(amount, 100000000000000000000000000000000000000000000000000000000000000000000)))))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465416d6f756e742829000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 23)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(and(iszero(iszero(iszero(eq(npk, 0)))), iszero(iszero(lt(npk, 21888242871839275222246405745257275088548364400416034343698204186575808495617))))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f74654e504b2829000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 20)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            stop()
        }
        function internal_internal_sumNoteAmounts(notes_data_offset, notes_length) -> __ret0 {
            let totalAmount := 0
            for {
                let i := 0
            } lt(i, notes_length) {
                i := add(i, 1)
            } {
                let amount := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, i, 3, 2)
                totalAmount := add(totalAmount, amount)
            }
            __ret0 := totalAmount
            leave
        }
        function internal_internal_addRelayer(relayer) {
            if iszero(eq(caller(), sload(1))) {
                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(4, 32)
                mstore(36, 38)
                mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                revert(0, 132)
            }
            if iszero(iszero(eq(relayer, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 19)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let already := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
            if iszero(eq(already, 0)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c52656c61796572416c72656164794163746976652829000000000000)
                    let __err_hash := keccak256(__err_ptr, 26)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 1)
            {
                let __evt_ptr := mload(64)
                mstore(add(__evt_ptr, 0), 0x52656c6179657241646465642861646472657373290000000000000000000000)
                let __evt_topic0 := keccak256(__evt_ptr, 21)
                log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
            }
            stop()
        }
        function internal_internal_removeRelayer(relayer) {
            if iszero(eq(caller(), sload(1))) {
                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(4, 32)
                mstore(36, 38)
                mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                revert(0, 132)
            }
            if iszero(iszero(eq(relayer, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 19)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let active := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
            if iszero(iszero(eq(active, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c556e617574686f72697a656452656c61796572282900000000000000)
                    let __err_hash := keccak256(__err_ptr, 25)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 0)
            {
                let __evt_ptr := mload(64)
                mstore(add(__evt_ptr, 0), 0x52656c6179657252656d6f766564286164647265737329000000000000000000)
                let __evt_topic0 := keccak256(__evt_ptr, 23)
                log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
            }
            stop()
        }
        function internal_internal_setVerifierRouter(verifierRouter) {
            if iszero(eq(caller(), sload(1))) {
                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(4, 32)
                mstore(36, 38)
                mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                revert(0, 132)
            }
            let previousRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
            {
                let __ite_cond := eq(previousRouter, verifierRouter)
                if __ite_cond {
                }
                if iszero(__ite_cond) {
                    if iszero(iszero(eq(verifierRouter, 0))) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                            let __err_hash := keccak256(__err_ptr, 19)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    sstore(97642014805756523509931909943000448576722218578626833372473198353469753044997, and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
                    {
                        let __evt_ptr := mload(64)
                        mstore(add(__evt_ptr, 0), 0x5665726966696572526f757465725570646174656428616464726573732c6164)
                        mstore(add(__evt_ptr, 32), 0x6472657373290000000000000000000000000000000000000000000000000000)
                        let __evt_topic0 := keccak256(__evt_ptr, 38)
                        log3(__evt_ptr, 0, __evt_topic0, and(previousRouter, 0xffffffffffffffffffffffffffffffffffffffff), and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
                    }
                }
            }
            stop()
        }
        function internal_internal_transferOwnership(newOwner) {
            if iszero(eq(caller(), sload(1))) {
                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                mstore(4, 32)
                mstore(36, 38)
                mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                revert(0, 132)
            }
            sstore(2, and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
            stop()
        }
        function internal_internal_acceptOwnership() {
            let sender := caller()
            let pending := sload(2)
            if iszero(eq(sender, pending)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x43616c6c65724e6f7450656e64696e674f776e65722829000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 23)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            sstore(1, and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
            sstore(2, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
            stop()
        }
        function internal_internal_countNonZero(values_data_offset, values_length, excludeIndex) -> __ret0 {
            let count := 0
            for {
                let j := 0
            } lt(j, values_length) {
                j := add(j, 1)
            } {
                if iszero(eq(j, excludeIndex)) {
                    let value := __verity_array_element_calldata_checked(values_data_offset, values_length, j)
                    if iszero(eq(value, 0)) {
                        count := add(count, 1)
                    }
                }
            }
            __ret0 := count
            leave
        }
        function internal_internal_spendNullifiers(nullifierHashes_data_offset, nullifierHashes_length) {
            for {
                let k := 0
            } lt(k, nullifierHashes_length) {
                k := add(k, 1)
            } {
                let nullifierHash := __verity_array_element_calldata_checked(nullifierHashes_data_offset, nullifierHashes_length, k)
                if iszero(eq(nullifierHash, 0)) {
                    sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044996, nullifierHash), 1)
                }
            }
            stop()
        }
        function internal_internal_lazyDefaultZero(index) -> __ret0 {
            let zero := 0
            if eq(index, 1) {
                zero := 14744269619966411208579211824598458697587494354926760081771325075741142829156
            }
            if eq(index, 2) {
                zero := 7423237065226347324353380772367382631490014989348495481811164164159255474657
            }
            if eq(index, 3) {
                zero := 11286972368698509976183087595462810875513684078608517520839298933882497716792
            }
            if eq(index, 4) {
                zero := 3607627140608796879659380071776844901612302623152076817094415224584923813162
            }
            if eq(index, 5) {
                zero := 19712377064642672829441595136074946683621277828620209496774504837737984048981
            }
            if eq(index, 6) {
                zero := 20775607673010627194014556968476266066927294572720319469184847051418138353016
            }
            if eq(index, 7) {
                zero := 3396914609616007258851405644437304192396347162513310381425243293
            }
            if eq(index, 8) {
                zero := 21551820661461729022865262380882070649935529853313286572328683688269863701601
            }
            if eq(index, 9) {
                zero := 6573136701248752079028194407151022595060682063033565181951145966236778420039
            }
            if eq(index, 10) {
                zero := 12413880268183407374852357075976609371175688755676981206018884971008854919922
            }
            if eq(index, 11) {
                zero := 14271763308400718165336499097156975241954733520325982997864342600795471836726
            }
            if eq(index, 12) {
                zero := 20066985985293572387227381049700832219069292839614107140851619262827735677018
            }
            if eq(index, 13) {
                zero := 9394776414966240069580838672673694685292165040808226440647796406499139370960
            }
            if eq(index, 14) {
                zero := 11331146992410411304059858900317123658895005918277453009197229807340014528524
            }
            if eq(index, 15) {
                zero := 15819538789928229930262697811477882737253464456578333862691129291651619515538
            }
            if eq(index, 16) {
                zero := 19217088683336594659449020493828377907203207941212636669271704950158751593251
            }
            if eq(index, 17) {
                zero := 21035245323335827719745544373081896983162834604456827698288649288827293579666
            }
            if eq(index, 18) {
                zero := 6939770416153240137322503476966641397417391950902474480970945462551409848591
            }
            if eq(index, 19) {
                zero := 10941962436777715901943463195175331263348098796018438960955633645115732864202
            }
            if eq(index, 20) {
                zero := 15019797232609675441998260052101280400536945603062888308240081994073687793470
            }
            if eq(index, 21) {
                zero := 11702828337982203149177882813338547876343922920234831094975924378932809409969
            }
            if eq(index, 22) {
                zero := 11217067736778784455593535811108456786943573747466706329920902520905755780395
            }
            if eq(index, 23) {
                zero := 16072238744996205792852194127671441602062027943016727953216607508365787157389
            }
            if eq(index, 24) {
                zero := 17681057402012993898104192736393849603097507831571622013521167331642182653248
            }
            if eq(index, 25) {
                zero := 21694045479371014653083846597424257852691458318143380497809004364947786214945
            }
            if eq(index, 26) {
                zero := 8163447297445169709687354538480474434591144168767135863541048304198280615192
            }
            if eq(index, 27) {
                zero := 14081762237856300239452543304351251708585712948734528663957353575674639038357
            }
            if eq(index, 28) {
                zero := 16619959921569409661790279042024627172199214148318086837362003702249041851090
            }
            if eq(index, 29) {
                zero := 7022159125197495734384997711896547675021391130223237843255817587255104160365
            }
            if eq(index, 30) {
                zero := 4114686047564160449611603615418567457008101555090703535405891656262658644463
            }
            if eq(index, 31) {
                zero := 12549363297364877722388257367377629555213421373705596078299904496781819142130
            }
            if eq(index, 32) {
                zero := 21443572485391568159800782191812935835534334817699172242223315142338162256601
            }
            __ret0 := zero
            leave
        }
        function internal_internal_lazyIndexForElement(level, index) -> __ret0 {
            __ret0 := add(mul(4294967295, level), index)
            leave
        }
        function internal_internal_lazyInsert(leaf) {
            let startIndex := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
            let maxIndex := and(shr(0, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
            if iszero(lt(leaf, 21888242871839275222246405745257275088548364400416034343698204186575808495617)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                    let __err_hash := keccak256(__err_ptr, 24)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(lt(startIndex, maxIndex)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                    let __err_hash := keccak256(__err_ptr, 24)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            {
                let __compat_value := add(startIndex, 1)
                let __compat_packed := and(__compat_value, 1099511627775)
                let __compat_slot_word := sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)
                let __compat_slot_cleared := and(__compat_slot_word, not(1208925819613529663078400))
                sstore(97642014805756523509931909943000448576722218578626833372473198353469753044993, or(__compat_slot_cleared, shl(40, __compat_packed)))
            }
            let index := startIndex
            let hash := leaf
            let active := 1
            for {
                let level := 0
            } lt(level, 32) {
                level := add(level, 1)
            } {
                if iszero(eq(active, 0)) {
                    let elementKey := internal_internal_lazyIndexForElement(level, index)
                    sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, elementKey), hash)
                    {
                        let __ite_cond := eq(and(index, 1), 0)
                        if __ite_cond {
                            active := 0
                        }
                        if iszero(__ite_cond) {
                            let siblingKey := internal_internal_lazyIndexForElement(level, sub(index, 1))
                            let sibling := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, siblingKey))
                            let parent := internal_internal_poseidon2(sibling, hash)
                            hash := parent
                            index := shr(1, index)
                        }
                    }
                }
            }
            stop()
        }
        function internal_internal_lazyRootWithDepth32() -> __ret0 {
            let numberOfLeaves := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
            {
                let __ite_cond := eq(numberOfLeaves, 0)
                if __ite_cond {
                    __ret0 := 21443572485391568159800782191812935835534334817699172242223315142338162256601
                    leave
                }
                if iszero(__ite_cond) {
                    let levels_length := 33
                    let levels_data_offset := add(mload(64), 32)
                    mstore(sub(levels_data_offset, 32), levels_length)
                    mstore(64, add(levels_data_offset, mul(levels_length, 32)))
                    let index := sub(numberOfLeaves, 1)
                    {
                        let __ite_cond := eq(and(index, 1), 0)
                        if __ite_cond {
                            let elementKey := internal_internal_lazyIndexForElement(0, index)
                            let element := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, elementKey))
                            mstore(add(levels_data_offset, mul(0, 32)), element)
                        }
                        if iszero(__ite_cond) {
                            mstore(add(levels_data_offset, mul(0, 32)), 0)
                        }
                    }
                    for {
                        let level := 0
                    } lt(level, 32) {
                        level := add(level, 1)
                    } {
                        let current := __verity_array_element_memory_checked(levels_data_offset, levels_length, level)
                        {
                            let __ite_cond := eq(and(index, 1), 0)
                            if __ite_cond {
                                let z := internal_internal_lazyDefaultZero(level)
                                let parent := internal_internal_poseidon2(current, z)
                                mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                            }
                            if iszero(__ite_cond) {
                                let levelCount := shr(add(level, 1), numberOfLeaves)
                                let parentIndex := shr(1, index)
                                {
                                    let __ite_cond := gt(levelCount, parentIndex)
                                    if __ite_cond {
                                        let parentKey := internal_internal_lazyIndexForElement(add(level, 1), parentIndex)
                                        let parent := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, parentKey))
                                        mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                                    }
                                    if iszero(__ite_cond) {
                                        let siblingKey := internal_internal_lazyIndexForElement(level, sub(index, 1))
                                        let sibling := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, siblingKey))
                                        let parent := internal_internal_poseidon2(sibling, current)
                                        mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                                    }
                                }
                            }
                        }
                        index := shr(1, index)
                    }
                    __ret0 := __verity_array_element_memory_checked(levels_data_offset, levels_length, 32)
                    leave
                }
            }
        }
        function internal_internal_insertLeaves(leafHashes_data_offset, leafHashes_length) -> __ret0 {
            let count := leafHashes_length
            {
                let __ite_cond := eq(count, 0)
                if __ite_cond {
                    let currentRoot := sload(97642014805756523509931909943000448576722218578626833372473198353469753044992)
                    __ret0 := currentRoot
                    leave
                }
                if iszero(__ite_cond) {
                    for {
                        let m := 0
                    } lt(m, count) {
                        m := add(m, 1)
                    } {
                        let leaf := __verity_array_element_calldata_checked(leafHashes_data_offset, leafHashes_length, m)
                        internal_internal_lazyInsert(leaf)
                    }
                }
            }
            let newRoot := internal_internal_lazyRootWithDepth32()
            sstore(97642014805756523509931909943000448576722218578626833372473198353469753044992, newRoot)
            sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044995, newRoot), 1)
            __ret0 := newRoot
            leave
        }
        function internal_internal_computeContextHash(ciphertexts_data_offset, ciphertexts_length) -> __ret0 {
            let cid := chainid()
            let selfAddr := address()
            {
                let __ciphertextsHash_abi_array_ptr := mload(64)
                mstore(__ciphertextsHash_abi_array_ptr, 32)
                mstore(add(__ciphertextsHash_abi_array_ptr, 32), ciphertexts_length)
                let __ciphertextsHash_abi_array_data_bytes := mul(ciphertexts_length, 128)
                calldatacopy(add(__ciphertextsHash_abi_array_ptr, 64), ciphertexts_data_offset, __ciphertextsHash_abi_array_data_bytes)
                let __ciphertextsHash_abi_array_total_bytes := add(64, __ciphertextsHash_abi_array_data_bytes)
                let __ciphertextsHash_abi_array_padded_total := and(add(__ciphertextsHash_abi_array_total_bytes, 31), not(31))
                mstore(64, add(__ciphertextsHash_abi_array_ptr, __ciphertextsHash_abi_array_padded_total))
                let ciphertextsHash := keccak256(__ciphertextsHash_abi_array_ptr, __ciphertextsHash_abi_array_total_bytes)
            }
            {
                let __packed_word_0 := cid
                let __packed_word_1 := selfAddr
                let __packed_word_2 := ciphertextsHash
                mstore(0, __packed_word_0)
                mstore(32, __packed_word_1)
                mstore(64, __packed_word_2)
            }
            let rawContext := keccak256(0, 96)
            __ret0 := mod(rawContext, 21888242871839275222246405745257275088548364400416034343698204186575808495617)
            leave
        }
        function internal_internal_validateContext(merkleRoot, contextHash, expectedContext) {
            if iszero(eq(contextHash, expectedContext)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964436f6e746578744861736828290000000000000000)
                    let __err_hash := keccak256(__err_ptr, 24)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let rootSeen := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044995, merkleRoot))
            if iszero(iszero(eq(rootSeen, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644d65726b6c65526f6f742829000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 23)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            stop()
        }
        function internal_internal_settleWithdrawalTransfer(token, recipient, amount) {
            let selfAddr := address()
            {
                mstore(0, shl(224, 0x70a08231))
                mstore(4, selfAddr)
                let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                if iszero(__balanceOf_success) {
                    let __balanceOf_rds := returndatasize()
                    returndatacopy(0, 0, __balanceOf_rds)
                    revert(0, __balanceOf_rds)
                }
                if iszero(eq(returndatasize(), 32)) {
                    revert(0, 0)
                }
            }
            let poolBefore := mload(0)
            {
                mstore(0, shl(224, 0x70a08231))
                mstore(4, recipient)
                let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                if iszero(__balanceOf_success) {
                    let __balanceOf_rds := returndatasize()
                    returndatacopy(0, 0, __balanceOf_rds)
                    revert(0, __balanceOf_rds)
                }
                if iszero(eq(returndatasize(), 32)) {
                    revert(0, 0)
                }
            }
            let recipientBefore := mload(0)
            {
                mstore(0, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                mstore(4, recipient)
                mstore(36, amount)
                let __st_success := call(gas(), token, 0, 0, 68, 0, 32)
                if iszero(__st_success) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 17)
                    mstore(68, 0x7472616e73666572207265766572746564000000000000000000000000000000)
                    revert(0, 100)
                }
                if eq(returndatasize(), 32) {
                    if iszero(mload(0)) {
                        mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                        mstore(4, 32)
                        mstore(36, 23)
                        mstore(68, 0x7472616e736665722072657475726e65642066616c7365000000000000000000)
                        revert(0, 100)
                    }
                }
            }
            {
                mstore(0, shl(224, 0x70a08231))
                mstore(4, selfAddr)
                let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                if iszero(__balanceOf_success) {
                    let __balanceOf_rds := returndatasize()
                    returndatacopy(0, 0, __balanceOf_rds)
                    revert(0, __balanceOf_rds)
                }
                if iszero(eq(returndatasize(), 32)) {
                    revert(0, 0)
                }
            }
            let poolAfter := mload(0)
            {
                mstore(0, shl(224, 0x70a08231))
                mstore(4, recipient)
                let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                if iszero(__balanceOf_success) {
                    let __balanceOf_rds := returndatasize()
                    returndatacopy(0, 0, __balanceOf_rds)
                    revert(0, __balanceOf_rds)
                }
                if iszero(eq(returndatasize(), 32)) {
                    revert(0, 0)
                }
            }
            let recipientAfter := mload(0)
            if iszero(eq(sub(poolBefore, poolAfter), amount)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c576974686472617742616c616e63654d69736d617463682829000000)
                    let __err_hash := keccak256(__err_ptr, 29)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(eq(sub(recipientAfter, recipientBefore), amount)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c576974686472617742616c616e63654d69736d617463682829000000)
                    let __err_hash := keccak256(__err_ptr, 29)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            stop()
        }
        function internal_internal_transferWithBalanceCheck(permit_0_0, permit_0_1, permit_1, permit_2, depositor, signature_data_offset, signature_length, totalAmount, witness) {
            let selfAddr := address()
            let token := permit_0_0
            {
                mstore(0, shl(224, 0x70a08231))
                mstore(4, selfAddr)
                let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                if iszero(__balanceOf_success) {
                    let __balanceOf_rds := returndatasize()
                    returndatacopy(0, 0, __balanceOf_rds)
                    revert(0, __balanceOf_rds)
                }
                if iszero(eq(returndatasize(), 32)) {
                    revert(0, 0)
                }
            }
            let balBefore := mload(0)
            let permitCallOk, permitAccepted := permitWitnessTransferFrom_try(sload(98021192859356073326120044313192698615125063568118942569962362705841075886849), token, permit_0_1, permit_1, permit_2, selfAddr, totalAmount, depositor, witness, signature_data_offset, signature_length)
            if iszero(permitCallOk) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                    let __err_hash := keccak256(__err_ptr, 28)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(permitAccepted) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                    let __err_hash := keccak256(__err_ptr, 28)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            {
                mstore(0, shl(224, 0x70a08231))
                mstore(4, selfAddr)
                let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                if iszero(__balanceOf_success) {
                    let __balanceOf_rds := returndatasize()
                    returndatacopy(0, 0, __balanceOf_rds)
                    revert(0, __balanceOf_rds)
                }
                if iszero(eq(returndatasize(), 32)) {
                    revert(0, 0)
                }
            }
            let balAfter := mload(0)
            if iszero(eq(sub(balAfter, balBefore), totalAmount)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                    let __err_hash := keccak256(__err_ptr, 28)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            stop()
        }
        function internal_internal_deposit(depositor, notes_data_offset, notes_length, ciphertexts_data_offset, ciphertexts_length, permit_0_0, permit_0_1, permit_1, permit_2, signature_data_offset, signature_length) {
            internal___modifier_onlyRelayer()
            let notesLen := notes_length
            if iszero(iszero(eq(notesLen, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c456d7074794e6f746573282900000000000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 16)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(eq(ciphertexts_length, notesLen)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                    let __err_hash := keccak256(__err_ptr, 29)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let newLeaves_length := notesLen
            let newLeaves_data_offset := add(mload(64), 32)
            mstore(sub(newLeaves_data_offset, 32), newLeaves_length)
            mstore(64, add(newLeaves_data_offset, mul(newLeaves_length, 32)))
            for {
                let noteIndex := 0
            } lt(noteIndex, notesLen) {
                noteIndex := add(noteIndex, 1)
            } {
                let npk := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 0)
                let token := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 1)
                let amount := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 2)
                internal_internal_validateNoteFields(npk, token, amount)
                if iszero(eq(token, permit_0_0)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c546f6b656e4d69736d61746368282900000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 19)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let leaf := internal_internal_hashNote(npk, token, amount)
                mstore(add(newLeaves_data_offset, mul(noteIndex, 32)), leaf)
            }
            let totalAmount := internal_internal_sumNoteAmounts(notes_data_offset, notes_length)
            let selfAddr := address()
            {
                let __notesHash_abi_two_arrays_ptr := mload(64)
                let __notesHash_abi_array_a_data_bytes := mul(notesLen, 96)
                let __notesHash_abi_array_b_data_bytes := mul(ciphertexts_length, 128)
                let __notesHash_abi_array_a_tail_bytes := add(32, __notesHash_abi_array_a_data_bytes)
                let __notesHash_abi_array_b_tail_bytes := add(32, __notesHash_abi_array_b_data_bytes)
                let __notesHash_abi_array_b_head_offset := add(64, __notesHash_abi_array_a_tail_bytes)
                let __notesHash_abi_two_arrays_total_bytes := add(__notesHash_abi_array_b_head_offset, __notesHash_abi_array_b_tail_bytes)
                mstore(__notesHash_abi_two_arrays_ptr, 64)
                mstore(add(__notesHash_abi_two_arrays_ptr, 32), __notesHash_abi_array_b_head_offset)
                mstore(add(__notesHash_abi_two_arrays_ptr, 64), notesLen)
                calldatacopy(add(__notesHash_abi_two_arrays_ptr, 96), notes_data_offset, __notesHash_abi_array_a_data_bytes)
                mstore(add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_array_b_head_offset), ciphertexts_length)
                calldatacopy(add(add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_array_b_head_offset), 32), ciphertexts_data_offset, __notesHash_abi_array_b_data_bytes)
                let __notesHash_abi_two_arrays_padded_total := and(add(__notesHash_abi_two_arrays_total_bytes, 31), not(31))
                mstore(64, add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_two_arrays_padded_total))
                let notesHash := keccak256(__notesHash_abi_two_arrays_ptr, __notesHash_abi_two_arrays_total_bytes)
            }
            {
                let __packed_word_0 := 85194627925618981451180140414236292804855281853588093248984713240396722975024
                let __packed_word_1 := selfAddr
                let __packed_word_2 := notesHash
                mstore(0, __packed_word_0)
                mstore(32, __packed_word_1)
                mstore(64, __packed_word_2)
            }
            let witness := keccak256(0, 96)
            internal_internal_transferWithBalanceCheck(permit_0_0, permit_0_1, permit_1, permit_2, depositor, signature_data_offset, signature_length, totalAmount, witness)
            let startIndex := internal_internal_nextLeafIndex()
            let newRoot := internal_internal_insertLeaves(newLeaves_data_offset, newLeaves_length)
            {
                let __evt_ptr := mload(64)
                mstore(add(__evt_ptr, 0), 0x4465706f736974656428616464726573732c75696e743235362c75696e743235)
                mstore(add(__evt_ptr, 32), 0x362c2875696e743235362c616464726573732c75696e74323536295b5d2c2875)
                mstore(add(__evt_ptr, 64), 0x696e743235362c75696e743235365b335d295b5d290000000000000000000000)
                let __evt_topic0 := keccak256(__evt_ptr, 85)
                let __evt_data_tail := 128
                mstore(add(__evt_ptr, 0), newRoot)
                mstore(add(__evt_ptr, 32), startIndex)
                mstore(add(__evt_ptr, 64), __evt_data_tail)
                let __evt_arg2_len := notes_length
                let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                mstore(__evt_arg2_dst, __evt_arg2_len)
                let __evt_arg2_byte_len := mul(__evt_arg2_len, 96)
                for {
                    let __evt_arg2_i := 0
                } lt(__evt_arg2_i, __evt_arg2_len) {
                    __evt_arg2_i := add(__evt_arg2_i, 1)
                } {
                    let __evt_arg2_elem_base := add(add(4, notes_offset), mul(__evt_arg2_i, 96))
                    let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 96))
                    mstore(add(__evt_arg2_out_base, 0), calldataload(add(__evt_arg2_elem_base, 0)))
                    mstore(add(__evt_arg2_out_base, 32), and(calldataload(add(__evt_arg2_elem_base, 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                    mstore(add(__evt_arg2_out_base, 64), calldataload(add(__evt_arg2_elem_base, 64)))
                }
                let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                mstore(add(__evt_ptr, 96), __evt_data_tail)
                let __evt_arg3_len := ciphertexts_length
                let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                mstore(__evt_arg3_dst, __evt_arg3_len)
                let __evt_arg3_byte_len := mul(__evt_arg3_len, 128)
                for {
                    let __evt_arg3_i := 0
                } lt(__evt_arg3_i, __evt_arg3_len) {
                    __evt_arg3_i := add(__evt_arg3_i, 1)
                } {
                    let __evt_arg3_elem_base := add(add(4, ciphertexts_offset), mul(__evt_arg3_i, 128))
                    let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 128))
                    mstore(add(__evt_arg3_out_base, 0), calldataload(add(__evt_arg3_elem_base, 0)))
                    mstore(add(__evt_arg3_out_base, 32), calldataload(add(__evt_arg3_elem_base, 32)))
                    mstore(add(__evt_arg3_out_base, 64), calldataload(add(__evt_arg3_elem_base, 64)))
                    mstore(add(__evt_arg3_out_base, 96), calldataload(add(__evt_arg3_elem_base, 96)))
                }
                let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                log2(__evt_ptr, __evt_data_tail, __evt_topic0, and(depositor, 0xffffffffffffffffffffffffffffffffffffffff))
            }
            stop()
        }
        function internal_internal_transfer(transactions_data_offset, transactions_length) {
            internal___modifier_onlyRelayer()
            let txLen := transactions_length
            if iszero(iszero(eq(txLen, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 23)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            for {
                let i := 0
            } lt(i, txLen) {
                i := add(i, 1)
            } {
                let verifierRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
                let success, circuit_verifier, circuit_inputCount, circuit_outputCount, circuit_active := getCircuit_try(verifierRouter, __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 8))
                if iszero(success) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                        let __err_hash := keccak256(__err_ptr, 26)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(circuit_verifier, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                        let __err_hash := keccak256(__err_ptr, 26)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(circuit_active, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c43697263756974496e61637469766528290000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 21)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10), circuit_inputCount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964496e70757453686170652829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11), circuit_outputCount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                        let __err_hash := keccak256(__err_ptr, 24)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let ciphertextCount := internal_internal_countNonZero(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 11), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
                if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13), ciphertextCount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let computedContext := internal_internal_computeContextHash(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 13), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13))
                internal_internal_validateContext(__verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 9), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 12), computedContext)
                let proofOk, ok := verifySpend_try(circuit_verifier, __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 0), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 1), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 2), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 3), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 4), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 5), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 6), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 7), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 9), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 12), __verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 11), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11))
                if iszero(proofOk) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(ok) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                internal_internal_spendNullifiers(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10))
                let leavesCount := 0
                for {
                    let commitCountIndex := 0
                } lt(commitCountIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11)) {
                    commitCountIndex := add(commitCountIndex, 1)
                } {
                    let commitment := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 11, commitCountIndex)
                    if iszero(eq(commitment, 0)) {
                        leavesCount := add(leavesCount, 1)
                    }
                }
                let leaves_length := leavesCount
                let leaves_data_offset := add(mload(64), 32)
                mstore(sub(leaves_data_offset, 32), leaves_length)
                mstore(64, add(leaves_data_offset, mul(leaves_length, 32)))
                let leafWriteIndex := 0
                for {
                    let commitWriteIndex := 0
                } lt(commitWriteIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11)) {
                    commitWriteIndex := add(commitWriteIndex, 1)
                } {
                    let commitment := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 11, commitWriteIndex)
                    if iszero(eq(commitment, 0)) {
                        mstore(add(leaves_data_offset, mul(leafWriteIndex, 32)), commitment)
                        leafWriteIndex := add(leafWriteIndex, 1)
                    }
                }
                let nullifierCount := 0
                for {
                    let nullifierCountIndex := 0
                } lt(nullifierCountIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10)) {
                    nullifierCountIndex := add(nullifierCountIndex, 1)
                } {
                    let nullifierHash := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 10, nullifierCountIndex)
                    if iszero(eq(nullifierHash, 0)) {
                        nullifierCount := add(nullifierCount, 1)
                    }
                }
                let realNulls_length := nullifierCount
                let realNulls_data_offset := add(mload(64), 32)
                mstore(sub(realNulls_data_offset, 32), realNulls_length)
                mstore(64, add(realNulls_data_offset, mul(realNulls_length, 32)))
                let nullifierWriteIndex := 0
                for {
                    let nullifierWriteIndexLoop := 0
                } lt(nullifierWriteIndexLoop, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10)) {
                    nullifierWriteIndexLoop := add(nullifierWriteIndexLoop, 1)
                } {
                    let nullifierHash := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 10, nullifierWriteIndexLoop)
                    if iszero(eq(nullifierHash, 0)) {
                        mstore(add(realNulls_data_offset, mul(nullifierWriteIndex, 32)), nullifierHash)
                        nullifierWriteIndex := add(nullifierWriteIndex, 1)
                    }
                }
                let startIndex := internal_internal_nextLeafIndex()
                let newRoot := internal_internal_insertLeaves(leaves_data_offset, leaves_length)
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x5472616e736665727265642875696e743235362c75696e743235362c75696e74)
                    mstore(add(__evt_ptr, 32), 0x3235365b5d2c75696e743235365b5d2c2875696e743235362c75696e74323536)
                    mstore(add(__evt_ptr, 64), 0x5b335d295b5d2900000000000000000000000000000000000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 71)
                    let __evt_data_tail := 128
                    mstore(add(__evt_ptr, 0), startIndex)
                    mstore(add(__evt_ptr, 32), __evt_data_tail)
                    let __evt_arg1_len := leaves_length
                    let __evt_arg1_dst := add(__evt_ptr, __evt_data_tail)
                    mstore(__evt_arg1_dst, __evt_arg1_len)
                    let __evt_arg1_byte_len := mul(__evt_arg1_len, 32)
                    for {
                        let __evt_arg1_i := 0
                    } lt(__evt_arg1_i, __evt_arg1_len) {
                        __evt_arg1_i := add(__evt_arg1_i, 1)
                    } {
                        let __evt_arg1_elem_base := add(leaves_data_offset, mul(__evt_arg1_i, 32))
                        let __evt_arg1_out_base := add(add(__evt_arg1_dst, 32), mul(__evt_arg1_i, 32))
                        mstore(add(__evt_arg1_out_base, 0), mload(add(__evt_arg1_elem_base, 0)))
                    }
                    let __evt_arg1_padded := and(add(__evt_arg1_byte_len, 31), not(31))
                    mstore(add(add(__evt_arg1_dst, 32), __evt_arg1_byte_len), 0)
                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg1_padded))
                    mstore(add(__evt_ptr, 64), __evt_data_tail)
                    let __evt_arg2_len := realNulls_length
                    let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                    mstore(__evt_arg2_dst, __evt_arg2_len)
                    let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                    for {
                        let __evt_arg2_i := 0
                    } lt(__evt_arg2_i, __evt_arg2_len) {
                        __evt_arg2_i := add(__evt_arg2_i, 1)
                    } {
                        let __evt_arg2_elem_base := add(realNulls_data_offset, mul(__evt_arg2_i, 32))
                        let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                        mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                    }
                    let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                    mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                    mstore(add(__evt_ptr, 96), __evt_data_tail)
                    let __evt_arg3_len := __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13)
                    let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                    mstore(__evt_arg3_dst, __evt_arg3_len)
                    let __evt_arg3_byte_len := mul(__evt_arg3_len, 128)
                    for {
                        let __evt_arg3_i := 0
                    } lt(__evt_arg3_i, __evt_arg3_len) {
                        __evt_arg3_i := add(__evt_arg3_i, 1)
                    } {
                        let __evt_arg3_elem_base := add(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 13), mul(__evt_arg3_i, 128))
                        let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 128))
                        mstore(add(__evt_arg3_out_base, 0), calldataload(add(__evt_arg3_elem_base, 0)))
                        mstore(add(__evt_arg3_out_base, 32), calldataload(add(__evt_arg3_elem_base, 32)))
                        mstore(add(__evt_arg3_out_base, 64), calldataload(add(__evt_arg3_elem_base, 64)))
                        mstore(add(__evt_arg3_out_base, 96), calldataload(add(__evt_arg3_elem_base, 96)))
                    }
                    let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                    mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                    log2(__evt_ptr, __evt_data_tail, __evt_topic0, newRoot)
                }
            }
            stop()
        }
        function internal_internal_executeWithdrawal(txn_data_offset, emergency) {
            if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15), 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465416d6f756e742829000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 23)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f74654e504b2829000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 20)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465546f6b656e282900000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 22)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if gt(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), 1461501637330902918203684832716283019655932542975) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c526563697069656e742829)
                    let __err_hash := keccak256(__err_ptr, 32)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let recipient := __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13)
            let selfAddr := address()
            if iszero(iszero(eq(recipient, selfAddr))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c526563697069656e742829)
                    let __err_hash := keccak256(__err_ptr, 32)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let verifierRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
            let success, circuit_verifier, circuit_inputCount, circuit_outputCount, circuit_active := getCircuit_try(verifierRouter, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 8))
            if iszero(success) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                    let __err_hash := keccak256(__err_ptr, 26)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(iszero(eq(circuit_verifier, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                    let __err_hash := keccak256(__err_ptr, 26)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(iszero(eq(circuit_active, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c43697263756974496e61637469766528290000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 21)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10), circuit_inputCount)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964496e70757453686170652829000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 23)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11), circuit_outputCount)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                    let __err_hash := keccak256(__err_ptr, 24)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let wSlot := sub(circuit_outputCount, 1)
            let withdrawalCommitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, wSlot)
            if iszero(iszero(eq(withdrawalCommitment, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c5769746864726177616c536c6f745a65726f28290000000000000000)
                    let __err_hash := keccak256(__err_ptr, 24)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let noteHash := internal_internal_hashNote(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15))
            if iszero(eq(withdrawalCommitment, noteHash)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c436f6d6d69746d656e7428)
                    mstore(add(__err_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 33)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let ciphertextCount := internal_internal_countNonZero(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 11), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11), wSlot)
            if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16), ciphertextCount)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                    let __err_hash := keccak256(__err_ptr, 29)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let computedContext := internal_internal_computeContextHash(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16))
            internal_internal_validateContext(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 9), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 12), computedContext)
            let proofOk, ok := verifySpend_try(circuit_verifier, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 0), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 1), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 2), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 3), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 4), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 5), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 6), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 7), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 9), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 12), __verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 11), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11))
            if iszero(proofOk) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                    let __err_hash := keccak256(__err_ptr, 29)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(ok) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                    let __err_hash := keccak256(__err_ptr, 29)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            internal_internal_spendNullifiers(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10))
            let leavesCount := 0
            for {
                let withdrawCommitCountIndex := 0
            } lt(withdrawCommitCountIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11)) {
                withdrawCommitCountIndex := add(withdrawCommitCountIndex, 1)
            } {
                let commitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, withdrawCommitCountIndex)
                if iszero(eq(withdrawCommitCountIndex, wSlot)) {
                    if iszero(eq(commitment, 0)) {
                        leavesCount := add(leavesCount, 1)
                    }
                }
            }
            let leaves_length := leavesCount
            let leaves_data_offset := add(mload(64), 32)
            mstore(sub(leaves_data_offset, 32), leaves_length)
            mstore(64, add(leaves_data_offset, mul(leaves_length, 32)))
            let leafWriteIndex := 0
            for {
                let withdrawCommitWriteIndex := 0
            } lt(withdrawCommitWriteIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11)) {
                withdrawCommitWriteIndex := add(withdrawCommitWriteIndex, 1)
            } {
                let commitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, withdrawCommitWriteIndex)
                if iszero(eq(withdrawCommitWriteIndex, wSlot)) {
                    if iszero(eq(commitment, 0)) {
                        mstore(add(leaves_data_offset, mul(leafWriteIndex, 32)), commitment)
                        leafWriteIndex := add(leafWriteIndex, 1)
                    }
                }
            }
            let nullifierCount := 0
            for {
                let withdrawNullifierCountIndex := 0
            } lt(withdrawNullifierCountIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10)) {
                withdrawNullifierCountIndex := add(withdrawNullifierCountIndex, 1)
            } {
                let nullifierHash := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 10, withdrawNullifierCountIndex)
                if iszero(eq(nullifierHash, 0)) {
                    nullifierCount := add(nullifierCount, 1)
                }
            }
            let realNulls_length := nullifierCount
            let realNulls_data_offset := add(mload(64), 32)
            mstore(sub(realNulls_data_offset, 32), realNulls_length)
            mstore(64, add(realNulls_data_offset, mul(realNulls_length, 32)))
            let nullifierWriteIndex := 0
            for {
                let withdrawNullifierWriteIndexLoop := 0
            } lt(withdrawNullifierWriteIndexLoop, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10)) {
                withdrawNullifierWriteIndexLoop := add(withdrawNullifierWriteIndexLoop, 1)
            } {
                let nullifierHash := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 10, withdrawNullifierWriteIndexLoop)
                if iszero(eq(nullifierHash, 0)) {
                    mstore(add(realNulls_data_offset, mul(nullifierWriteIndex, 32)), nullifierHash)
                    nullifierWriteIndex := add(nullifierWriteIndex, 1)
                }
            }
            let startIndex := internal_internal_nextLeafIndex()
            let newRoot := internal_internal_insertLeaves(leaves_data_offset, leaves_length)
            internal_internal_settleWithdrawalTransfer(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), recipient, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15))
            {
                let __ite_cond := emergency
                if __ite_cond {
                    {
                        let __evt_ptr := mload(64)
                        mstore(add(__evt_ptr, 0), 0x456d657267656e637957697468647261776e28616464726573732c2875696e74)
                        mstore(add(__evt_ptr, 32), 0x3235362c616464726573732c75696e74323536292c75696e743235362c75696e)
                        mstore(add(__evt_ptr, 64), 0x743235362c75696e743235365b5d2c75696e743235365b5d2c2875696e743235)
                        mstore(add(__evt_ptr, 96), 0x362c75696e743235365b335d295b5d2900000000000000000000000000000000)
                        let __evt_topic0 := keccak256(__evt_ptr, 112)
                        let __evt_data_tail := 224
                        mstore(add(add(__evt_ptr, 0), 0), calldataload(add(add(txn_data_offset, 416), 0)))
                        mstore(add(add(__evt_ptr, 0), 32), and(calldataload(add(add(txn_data_offset, 416), 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(add(add(__evt_ptr, 0), 64), calldataload(add(add(txn_data_offset, 416), 64)))
                        mstore(add(__evt_ptr, 96), startIndex)
                        mstore(add(__evt_ptr, 128), __evt_data_tail)
                        let __evt_arg2_len := leaves_length
                        let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg2_dst, __evt_arg2_len)
                        let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                        for {
                            let __evt_arg2_i := 0
                        } lt(__evt_arg2_i, __evt_arg2_len) {
                            __evt_arg2_i := add(__evt_arg2_i, 1)
                        } {
                            let __evt_arg2_elem_base := add(leaves_data_offset, mul(__evt_arg2_i, 32))
                            let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                            mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                        }
                        let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                        mstore(add(__evt_ptr, 160), __evt_data_tail)
                        let __evt_arg3_len := realNulls_length
                        let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg3_dst, __evt_arg3_len)
                        let __evt_arg3_byte_len := mul(__evt_arg3_len, 32)
                        for {
                            let __evt_arg3_i := 0
                        } lt(__evt_arg3_i, __evt_arg3_len) {
                            __evt_arg3_i := add(__evt_arg3_i, 1)
                        } {
                            let __evt_arg3_elem_base := add(realNulls_data_offset, mul(__evt_arg3_i, 32))
                            let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 32))
                            mstore(add(__evt_arg3_out_base, 0), mload(add(__evt_arg3_elem_base, 0)))
                        }
                        let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                        mstore(add(__evt_ptr, 192), __evt_data_tail)
                        let __evt_arg4_len := __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16)
                        let __evt_arg4_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg4_dst, __evt_arg4_len)
                        let __evt_arg4_byte_len := mul(__evt_arg4_len, 128)
                        for {
                            let __evt_arg4_i := 0
                        } lt(__evt_arg4_i, __evt_arg4_len) {
                            __evt_arg4_i := add(__evt_arg4_i, 1)
                        } {
                            let __evt_arg4_elem_base := add(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), mul(__evt_arg4_i, 128))
                            let __evt_arg4_out_base := add(add(__evt_arg4_dst, 32), mul(__evt_arg4_i, 128))
                            mstore(add(__evt_arg4_out_base, 0), calldataload(add(__evt_arg4_elem_base, 0)))
                            mstore(add(__evt_arg4_out_base, 32), calldataload(add(__evt_arg4_elem_base, 32)))
                            mstore(add(__evt_arg4_out_base, 64), calldataload(add(__evt_arg4_elem_base, 64)))
                            mstore(add(__evt_arg4_out_base, 96), calldataload(add(__evt_arg4_elem_base, 96)))
                        }
                        let __evt_arg4_padded := and(add(__evt_arg4_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg4_dst, 32), __evt_arg4_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg4_padded))
                        log3(__evt_ptr, __evt_data_tail, __evt_topic0, and(recipient, 0xffffffffffffffffffffffffffffffffffffffff), newRoot)
                    }
                }
                if iszero(__ite_cond) {
                    {
                        let __evt_ptr := mload(64)
                        mstore(add(__evt_ptr, 0), 0x57697468647261776e28616464726573732c2875696e743235362c6164647265)
                        mstore(add(__evt_ptr, 32), 0x73732c75696e74323536292c75696e743235362c75696e743235362c75696e74)
                        mstore(add(__evt_ptr, 64), 0x3235365b5d2c75696e743235365b5d2c2875696e743235362c75696e74323536)
                        mstore(add(__evt_ptr, 96), 0x5b335d295b5d2900000000000000000000000000000000000000000000000000)
                        let __evt_topic0 := keccak256(__evt_ptr, 103)
                        let __evt_data_tail := 224
                        mstore(add(add(__evt_ptr, 0), 0), calldataload(add(add(txn_data_offset, 416), 0)))
                        mstore(add(add(__evt_ptr, 0), 32), and(calldataload(add(add(txn_data_offset, 416), 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(add(add(__evt_ptr, 0), 64), calldataload(add(add(txn_data_offset, 416), 64)))
                        mstore(add(__evt_ptr, 96), startIndex)
                        mstore(add(__evt_ptr, 128), __evt_data_tail)
                        let __evt_arg2_len := leaves_length
                        let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg2_dst, __evt_arg2_len)
                        let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                        for {
                            let __evt_arg2_i := 0
                        } lt(__evt_arg2_i, __evt_arg2_len) {
                            __evt_arg2_i := add(__evt_arg2_i, 1)
                        } {
                            let __evt_arg2_elem_base := add(leaves_data_offset, mul(__evt_arg2_i, 32))
                            let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                            mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                        }
                        let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                        mstore(add(__evt_ptr, 160), __evt_data_tail)
                        let __evt_arg3_len := realNulls_length
                        let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg3_dst, __evt_arg3_len)
                        let __evt_arg3_byte_len := mul(__evt_arg3_len, 32)
                        for {
                            let __evt_arg3_i := 0
                        } lt(__evt_arg3_i, __evt_arg3_len) {
                            __evt_arg3_i := add(__evt_arg3_i, 1)
                        } {
                            let __evt_arg3_elem_base := add(realNulls_data_offset, mul(__evt_arg3_i, 32))
                            let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 32))
                            mstore(add(__evt_arg3_out_base, 0), mload(add(__evt_arg3_elem_base, 0)))
                        }
                        let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                        mstore(add(__evt_ptr, 192), __evt_data_tail)
                        let __evt_arg4_len := __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16)
                        let __evt_arg4_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg4_dst, __evt_arg4_len)
                        let __evt_arg4_byte_len := mul(__evt_arg4_len, 128)
                        for {
                            let __evt_arg4_i := 0
                        } lt(__evt_arg4_i, __evt_arg4_len) {
                            __evt_arg4_i := add(__evt_arg4_i, 1)
                        } {
                            let __evt_arg4_elem_base := add(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), mul(__evt_arg4_i, 128))
                            let __evt_arg4_out_base := add(add(__evt_arg4_dst, 32), mul(__evt_arg4_i, 128))
                            mstore(add(__evt_arg4_out_base, 0), calldataload(add(__evt_arg4_elem_base, 0)))
                            mstore(add(__evt_arg4_out_base, 32), calldataload(add(__evt_arg4_elem_base, 32)))
                            mstore(add(__evt_arg4_out_base, 64), calldataload(add(__evt_arg4_elem_base, 64)))
                            mstore(add(__evt_arg4_out_base, 96), calldataload(add(__evt_arg4_elem_base, 96)))
                        }
                        let __evt_arg4_padded := and(add(__evt_arg4_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg4_dst, 32), __evt_arg4_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg4_padded))
                        log3(__evt_ptr, __evt_data_tail, __evt_topic0, and(recipient, 0xffffffffffffffffffffffffffffffffffffffff), newRoot)
                    }
                }
            }
            stop()
        }
        function internal_internal_withdraw(transactions_data_offset, transactions_length) {
            internal___modifier_onlyRelayer()
            let txLen := transactions_length
            if iszero(iszero(eq(txLen, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 23)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            for {
                let i := 0
            } lt(i, txLen) {
                i := add(i, 1)
            } {
                internal_internal_executeWithdrawal(__verity_array_element_dynamic_data_offset_calldata_checked(transactions_data_offset, transactions_length, i), 0)
            }
            stop()
        }
        function internal_internal_emergencyWithdraw(transactions_data_offset, transactions_length) {
            let txLen := transactions_length
            if iszero(iszero(eq(txLen, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 23)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            for {
                let i := 0
            } lt(i, txLen) {
                i := add(i, 1)
            } {
                internal_internal_executeWithdrawal(__verity_array_element_dynamic_data_offset_calldata_checked(transactions_data_offset, transactions_length, i), 1)
            }
            stop()
        }
        function internal___modifier_onlyRelayer() {
            let sender := caller()
            let isR := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, sender))
            if iszero(iszero(eq(isR, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c556e617574686f72697a656452656c61796572282900000000000000)
                    let __err_hash := keccak256(__err_ptr, 25)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            stop()
        }
        let argsOffset := add(dataoffset("runtime"), datasize("runtime"))
        let argsSize := sub(codesize(), argsOffset)
        codecopy(0, argsOffset, argsSize)
        if lt(argsSize, 32) {
            revert(0, 0)
        }
        let permit2 := and(mload(0), 0xffffffffffffffffffffffffffffffffffffffff)
        let arg0 := permit2
        sstore(98021192859356073326120044313192698615125063568118942569962362705841075886849, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
        if iszero(iszero(eq(permit2, 0))) {
            {
                let __err_ptr := mload(64)
                mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                let __err_hash := keccak256(__err_ptr, 19)
                let __err_selector := shl(224, shr(224, __err_hash))
                mstore(0, __err_selector)
                let __err_tail := 0
                revert(0, add(4, __err_tail))
            }
        }
        let codeLen := extcodesize(permit2)
        if iszero(iszero(eq(codeLen, 0))) {
            {
                let __err_ptr := mload(64)
                mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                let __err_hash := keccak256(__err_ptr, 19)
                let __err_selector := shl(224, shr(224, __err_hash))
                mstore(0, __err_selector)
                let __err_tail := 0
                revert(0, add(4, __err_tail))
            }
        }
        sstore(0, 255)
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            function poseidonT3(lhs, rhs) -> result {
                result := add(xor(lhs, rhs), 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef)
            }
            function poseidonT4(a, b, c) -> result {
                result := add(xor(xor(a, b), c), 0xfedcba0987654321fedcba0987654321fedcba0987654321fedcba0987654321)
            }
            function permitWitnessTransferFrom_try(permit2, token, permittedAmount, nonce, deadline, spender, amount, depositor, witness, signature, signatureLength) -> success, accepted {
                success := 1
                accepted := 1
            }
            function getCircuit_try(verifierRouter, circuitId) -> success, verifier, inputCount, outputCount, active {
                success := 1
                verifier := verifierRouter
                inputCount := 10
                outputCount := 4
                active := 1
            }
            function verifySpend_try(verifier, proofDataOffset, proofDataLength, proofA0, proofA1, proofB00, proofB01, proofB10, proofB11, proofC0, proofC1, merkleRoot, contextHash, nullifierHashes, newCommitments) -> success, ok {
                success := 1
                ok := 1
            }
            function mappingSlot(baseSlot, key) -> slot {
                mstore(0, key)
                mstore(32, baseSlot)
                slot := keccak256(0, 64)
            }
            function __verity_array_element_calldata_checked(data_offset, length, index) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                word := calldataload(add(data_offset, mul(index, 32)))
            }
            function __verity_array_element_memory_checked(data_offset, length, index) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                word := mload(add(data_offset, mul(index, 32)))
            }
            function __verity_array_element_word_calldata_checked(data_offset, length, index, element_words, word_offset) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                word := calldataload(add(data_offset, mul(add(mul(index, element_words), word_offset), 32)))
            }
            function __verity_array_element_word_memory_checked(data_offset, length, index, element_words, word_offset) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                word := mload(add(data_offset, mul(add(mul(index, element_words), word_offset), 32)))
            }
            function __verity_array_element_dynamic_word_calldata_checked(data_offset, length, index, word_offset) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_word_pos := add(add(data_offset, __element_rel_offset), mul(word_offset, 32))
                if gt(__element_word_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := calldataload(__element_word_pos)
            }
            function __verity_array_element_dynamic_word_memory_checked(data_offset, length, index, word_offset) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_word_pos := add(add(data_offset, __element_rel_offset), mul(word_offset, 32))
                word := mload(__element_word_pos)
            }
            function __verity_array_element_dynamic_data_offset_calldata_checked(data_offset, length, index) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_head_pos := add(data_offset, __element_rel_offset)
                if gt(__element_head_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := __element_head_pos
            }
            function __verity_array_element_dynamic_data_offset_memory_checked(data_offset, length, index) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_head_pos := add(data_offset, __element_rel_offset)
                word := __element_head_pos
            }
            function __verity_array_element_dynamic_member_length_calldata_checked(data_offset, length, index, word_offset) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_head_pos := add(data_offset, __element_rel_offset)
                let __member_rel_offset := calldataload(add(__element_head_pos, mul(word_offset, 32)))
                let __member_data_pos := add(__element_head_pos, __member_rel_offset)
                if gt(__member_data_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := calldataload(__member_data_pos)
            }
            function __verity_array_element_dynamic_member_length_memory_checked(data_offset, length, index, word_offset) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_head_pos := add(data_offset, __element_rel_offset)
                let __member_rel_offset := mload(add(__element_head_pos, mul(word_offset, 32)))
                let __member_data_pos := add(__element_head_pos, __member_rel_offset)
                word := mload(__member_data_pos)
            }
            function __verity_array_element_dynamic_member_data_offset_calldata_checked(data_offset, length, index, word_offset) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_head_pos := add(data_offset, __element_rel_offset)
                let __member_rel_offset := calldataload(add(__element_head_pos, mul(word_offset, 32)))
                let __member_data_pos := add(__element_head_pos, __member_rel_offset)
                if gt(__member_data_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := add(__member_data_pos, 32)
            }
            function __verity_array_element_dynamic_member_data_offset_memory_checked(data_offset, length, index, word_offset) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_head_pos := add(data_offset, __element_rel_offset)
                let __member_rel_offset := mload(add(__element_head_pos, mul(word_offset, 32)))
                let __member_data_pos := add(__element_head_pos, __member_rel_offset)
                word := add(__member_data_pos, 32)
            }
            function __verity_array_element_dynamic_member_element_calldata_checked(data_offset, length, index, word_offset, inner_index) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := calldataload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_head_pos := add(data_offset, __element_rel_offset)
                let __member_rel_offset := calldataload(add(__element_head_pos, mul(word_offset, 32)))
                let __member_data_pos := add(__element_head_pos, __member_rel_offset)
                let __member_length := calldataload(__member_data_pos)
                if iszero(lt(inner_index, __member_length)) {
                    revert(0, 0)
                }
                let __word_pos := add(__member_data_pos, add(32, mul(inner_index, 32)))
                if gt(__word_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := calldataload(__word_pos)
            }
            function __verity_array_element_dynamic_member_element_memory_checked(data_offset, length, index, word_offset, inner_index) -> word {
                if iszero(lt(index, length)) {
                    revert(0, 0)
                }
                let __element_rel_offset := mload(add(data_offset, mul(index, 32)))
                if lt(__element_rel_offset, mul(length, 32)) {
                    revert(0, 0)
                }
                let __element_head_pos := add(data_offset, __element_rel_offset)
                let __member_rel_offset := mload(add(__element_head_pos, mul(word_offset, 32)))
                let __member_data_pos := add(__element_head_pos, __member_rel_offset)
                let __member_length := mload(__member_data_pos)
                if iszero(lt(inner_index, __member_length)) {
                    revert(0, 0)
                }
                let __word_pos := add(__member_data_pos, add(32, mul(inner_index, 32)))
                word := mload(__word_pos)
            }
            function __verity_param_dynamic_head_word_calldata_checked(data_offset, word_offset) -> word {
                let __head_word_pos := add(data_offset, mul(word_offset, 32))
                if gt(__head_word_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := calldataload(__head_word_pos)
            }
            function __verity_param_dynamic_head_word_memory_checked(data_offset, word_offset) -> word {
                let __head_word_pos := add(data_offset, mul(word_offset, 32))
                word := mload(__head_word_pos)
            }
            function __verity_param_dynamic_member_length_calldata_checked(data_offset, word_offset) -> word {
                let __member_rel_offset := calldataload(add(data_offset, mul(word_offset, 32)))
                let __member_data_pos := add(data_offset, __member_rel_offset)
                if gt(__member_data_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := calldataload(__member_data_pos)
            }
            function __verity_param_dynamic_member_length_memory_checked(data_offset, word_offset) -> word {
                let __member_rel_offset := mload(add(data_offset, mul(word_offset, 32)))
                let __member_data_pos := add(data_offset, __member_rel_offset)
                word := mload(__member_data_pos)
            }
            function __verity_param_dynamic_member_data_offset_calldata_checked(data_offset, word_offset) -> word {
                let __member_rel_offset := calldataload(add(data_offset, mul(word_offset, 32)))
                let __member_data_pos := add(data_offset, __member_rel_offset)
                if gt(__member_data_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := add(__member_data_pos, 32)
            }
            function __verity_param_dynamic_member_data_offset_memory_checked(data_offset, word_offset) -> word {
                let __member_rel_offset := mload(add(data_offset, mul(word_offset, 32)))
                let __member_data_pos := add(data_offset, __member_rel_offset)
                word := add(__member_data_pos, 32)
            }
            function __verity_param_dynamic_member_element_calldata_checked(data_offset, word_offset, inner_index) -> word {
                let __member_rel_offset := calldataload(add(data_offset, mul(word_offset, 32)))
                let __member_data_pos := add(data_offset, __member_rel_offset)
                let __member_length := calldataload(__member_data_pos)
                if iszero(lt(inner_index, __member_length)) {
                    revert(0, 0)
                }
                let __word_pos := add(__member_data_pos, add(32, mul(inner_index, 32)))
                if gt(__word_pos, sub(calldatasize(), 32)) {
                    revert(0, 0)
                }
                word := calldataload(__word_pos)
            }
            function __verity_param_dynamic_member_element_memory_checked(data_offset, word_offset, inner_index) -> word {
                let __member_rel_offset := mload(add(data_offset, mul(word_offset, 32)))
                let __member_data_pos := add(data_offset, __member_rel_offset)
                let __member_length := mload(__member_data_pos)
                if iszero(lt(inner_index, __member_length)) {
                    revert(0, 0)
                }
                let __word_pos := add(__member_data_pos, add(32, mul(inner_index, 32)))
                word := mload(__word_pos)
            }
            function internal_internal_initialize(verifierRouter, ownerAddr, relayer) {
                if iszero(eq(sload(0), 0)) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 23)
                    mstore(68, 0x696e697469616c697a657220616c72656164792072756e000000000000000000)
                    revert(0, 100)
                }
                sstore(0, 1)
                let qMinusG1Y := 21888242871839275222246405745257275088696311157297823662689037894645226208581
                let g2x1 := 11559732032986387107991004021392285783925812861821192530917403151452391805634
                let g2x2 := 10857046999023057135944570762232829481370756359578518086990519993285655852781
                let g2y1 := 4082367875863433681332203403145435568316851327593401208105741076214120093531
                let g2y2 := 8495653923123431417604973247489272438418190587263600148770280649306958101930
                mstore(0, 1)
                mstore(32, 2)
                mstore(64, g2x1)
                mstore(96, g2x2)
                mstore(128, g2y1)
                mstore(160, g2y2)
                mstore(192, 1)
                mstore(224, qMinusG1Y)
                mstore(256, g2x1)
                mstore(288, g2x2)
                mstore(320, g2y1)
                mstore(352, g2y2)
                let pairA := 0
                {
                    let __bn256_pairing_output_offset := 0
                    let __bn256_pairing_success := staticcall(gas(), 8, 0, 384, __bn256_pairing_output_offset, 32)
                    if iszero(__bn256_pairing_success) {
                        revert(0, 0)
                    }
                    pairA := mload(__bn256_pairing_output_offset)
                }
                if iszero(eq(pairA, 1)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                mstore(0, 1)
                mstore(32, 2)
                let pairB := 0
                {
                    let __bn256_pairing_output_offset := 0
                    let __bn256_pairing_success := staticcall(gas(), 8, 0, 192, __bn256_pairing_output_offset, 32)
                    if iszero(__bn256_pairing_success) {
                        revert(0, 0)
                    }
                    pairB := mload(__bn256_pairing_output_offset)
                }
                if iszero(eq(pairB, 0)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let twoG1x := 1368015179489954701390400359078579693043519447331113978918064868415326638035
                let twoG1y := 9918110051302171585080402603319702774565515993150576347155970296011118125764
                let mul2x := 0
                let mul2y := 0
                {
                    mstore(0, 1)
                    mstore(32, 2)
                    mstore(64, 2)
                    let __bn256_mul_success := staticcall(gas(), 7, 0, 96, 0, 64)
                    if iszero(__bn256_mul_success) {
                        revert(0, 0)
                    }
                    mul2x := mload(0)
                    mul2y := mload(32)
                }
                if iszero(eq(mul2x, twoG1x)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(mul2y, twoG1y)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let mul3x := 0
                let mul3y := 0
                {
                    mstore(0, 1)
                    mstore(32, 2)
                    mstore(64, 3)
                    let __bn256_mul_success := staticcall(gas(), 7, 0, 96, 0, 64)
                    if iszero(__bn256_mul_success) {
                        revert(0, 0)
                    }
                    mul3x := mload(0)
                    mul3y := mload(32)
                }
                if iszero(or(iszero(iszero(iszero(eq(mul3x, twoG1x)))), iszero(iszero(iszero(eq(mul3y, twoG1y)))))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let add2x := 0
                let add2y := 0
                {
                    mstore(0, 1)
                    mstore(32, 2)
                    mstore(64, 1)
                    mstore(96, 2)
                    let __bn256_add_success := staticcall(gas(), 6, 0, 128, 0, 64)
                    if iszero(__bn256_add_success) {
                        revert(0, 0)
                    }
                    add2x := mload(0)
                    add2y := mload(32)
                }
                if iszero(eq(add2x, twoG1x)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(add2y, twoG1y)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let add3x := 0
                let add3y := 0
                {
                    mstore(0, 1)
                    mstore(32, 2)
                    mstore(64, twoG1x)
                    mstore(96, twoG1y)
                    let __bn256_add_success := staticcall(gas(), 6, 0, 128, 0, 64)
                    if iszero(__bn256_add_success) {
                        revert(0, 0)
                    }
                    add3x := mload(0)
                    add3y := mload(32)
                }
                if iszero(or(iszero(iszero(iszero(eq(add3x, twoG1x)))), iszero(iszero(iszero(eq(add3y, twoG1y)))))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(mul3x, add3x)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(mul3y, add3y)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                        let __err_hash := keccak256(__err_ptr, 27)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                sstore(1, and(ownerAddr, 0xffffffffffffffffffffffffffffffffffffffff))
                sstore(2, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
                if iszero(iszero(eq(verifierRouter, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 19)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                sstore(97642014805756523509931909943000448576722218578626833372473198353469753044997, and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
                if iszero(iszero(eq(relayer, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 19)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let already := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
                if iszero(eq(already, 0)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c52656c61796572416c72656164794163746976652829000000000000)
                        let __err_hash := keccak256(__err_ptr, 26)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 1)
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x52656c6179657241646465642861646472657373290000000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 21)
                    log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
                }
                stop()
            }
            function internal_internal_authorizeUpgrade(_newImplementation) {
                if iszero(eq(caller(), sload(1))) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 38)
                    mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                    mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                    revert(0, 132)
                }
                stop()
            }
            function internal_internal_renounceOwnership() {
                if iszero(eq(caller(), sload(1))) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 38)
                    mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                    mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                    revert(0, 132)
                }
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x506f6f6c52656e6f756e63654f776e65727368697044697361626c6564282900)
                    let __err_hash := keccak256(__err_ptr, 31)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
                stop()
            }
            function internal_internal_isRelayer(account) -> __ret0 {
                let r := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, account))
                __ret0 := r
                leave
            }
            function internal_internal_nextLeafIndex() -> __ret0 {
                let n := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
                __ret0 := n
                leave
            }
            function internal_internal_hashNote(npk, _token, amount) -> __ret0 {
                __ret0 := poseidonT4(npk, _token, amount)
                leave
            }
            function internal_internal_poseidon2(lhs, rhs) -> __ret0 {
                __ret0 := poseidonT3(lhs, rhs)
                leave
            }
            function internal_internal_validateNoteFields(npk, token, amount) {
                if iszero(iszero(eq(token, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465546f6b656e282900000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 22)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(and(iszero(iszero(iszero(eq(amount, 0)))), iszero(iszero(iszero(gt(amount, 100000000000000000000000000000000000000000000000000000000000000000000)))))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465416d6f756e742829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(and(iszero(iszero(iszero(eq(npk, 0)))), iszero(iszero(lt(npk, 21888242871839275222246405745257275088548364400416034343698204186575808495617))))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f74654e504b2829000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 20)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                stop()
            }
            function internal_internal_sumNoteAmounts(notes_data_offset, notes_length) -> __ret0 {
                let totalAmount := 0
                for {
                    let i := 0
                } lt(i, notes_length) {
                    i := add(i, 1)
                } {
                    let amount := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, i, 3, 2)
                    totalAmount := add(totalAmount, amount)
                }
                __ret0 := totalAmount
                leave
            }
            function internal_internal_addRelayer(relayer) {
                if iszero(eq(caller(), sload(1))) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 38)
                    mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                    mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                    revert(0, 132)
                }
                if iszero(iszero(eq(relayer, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 19)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let already := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
                if iszero(eq(already, 0)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c52656c61796572416c72656164794163746976652829000000000000)
                        let __err_hash := keccak256(__err_ptr, 26)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 1)
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x52656c6179657241646465642861646472657373290000000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 21)
                    log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
                }
                stop()
            }
            function internal_internal_removeRelayer(relayer) {
                if iszero(eq(caller(), sload(1))) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 38)
                    mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                    mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                    revert(0, 132)
                }
                if iszero(iszero(eq(relayer, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 19)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let active := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
                if iszero(iszero(eq(active, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c556e617574686f72697a656452656c61796572282900000000000000)
                        let __err_hash := keccak256(__err_ptr, 25)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 0)
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x52656c6179657252656d6f766564286164647265737329000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 23)
                    log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
                }
                stop()
            }
            function internal_internal_setVerifierRouter(verifierRouter) {
                if iszero(eq(caller(), sload(1))) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 38)
                    mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                    mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                    revert(0, 132)
                }
                let previousRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
                {
                    let __ite_cond := eq(previousRouter, verifierRouter)
                    if __ite_cond {
                    }
                    if iszero(__ite_cond) {
                        if iszero(iszero(eq(verifierRouter, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 19)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        sstore(97642014805756523509931909943000448576722218578626833372473198353469753044997, and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x5665726966696572526f757465725570646174656428616464726573732c6164)
                            mstore(add(__evt_ptr, 32), 0x6472657373290000000000000000000000000000000000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 38)
                            log3(__evt_ptr, 0, __evt_topic0, and(previousRouter, 0xffffffffffffffffffffffffffffffffffffffff), and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
                        }
                    }
                }
                stop()
            }
            function internal_internal_transferOwnership(newOwner) {
                if iszero(eq(caller(), sload(1))) {
                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                    mstore(4, 32)
                    mstore(36, 38)
                    mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                    mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                    revert(0, 132)
                }
                sstore(2, and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
                stop()
            }
            function internal_internal_acceptOwnership() {
                let sender := caller()
                let pending := sload(2)
                if iszero(eq(sender, pending)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x43616c6c65724e6f7450656e64696e674f776e65722829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                sstore(1, and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
                sstore(2, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
                stop()
            }
            function internal_internal_countNonZero(values_data_offset, values_length, excludeIndex) -> __ret0 {
                let count := 0
                for {
                    let j := 0
                } lt(j, values_length) {
                    j := add(j, 1)
                } {
                    if iszero(eq(j, excludeIndex)) {
                        let value := __verity_array_element_calldata_checked(values_data_offset, values_length, j)
                        if iszero(eq(value, 0)) {
                            count := add(count, 1)
                        }
                    }
                }
                __ret0 := count
                leave
            }
            function internal_internal_spendNullifiers(nullifierHashes_data_offset, nullifierHashes_length) {
                for {
                    let k := 0
                } lt(k, nullifierHashes_length) {
                    k := add(k, 1)
                } {
                    let nullifierHash := __verity_array_element_calldata_checked(nullifierHashes_data_offset, nullifierHashes_length, k)
                    if iszero(eq(nullifierHash, 0)) {
                        sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044996, nullifierHash), 1)
                    }
                }
                stop()
            }
            function internal_internal_lazyDefaultZero(index) -> __ret0 {
                let zero := 0
                if eq(index, 1) {
                    zero := 14744269619966411208579211824598458697587494354926760081771325075741142829156
                }
                if eq(index, 2) {
                    zero := 7423237065226347324353380772367382631490014989348495481811164164159255474657
                }
                if eq(index, 3) {
                    zero := 11286972368698509976183087595462810875513684078608517520839298933882497716792
                }
                if eq(index, 4) {
                    zero := 3607627140608796879659380071776844901612302623152076817094415224584923813162
                }
                if eq(index, 5) {
                    zero := 19712377064642672829441595136074946683621277828620209496774504837737984048981
                }
                if eq(index, 6) {
                    zero := 20775607673010627194014556968476266066927294572720319469184847051418138353016
                }
                if eq(index, 7) {
                    zero := 3396914609616007258851405644437304192396347162513310381425243293
                }
                if eq(index, 8) {
                    zero := 21551820661461729022865262380882070649935529853313286572328683688269863701601
                }
                if eq(index, 9) {
                    zero := 6573136701248752079028194407151022595060682063033565181951145966236778420039
                }
                if eq(index, 10) {
                    zero := 12413880268183407374852357075976609371175688755676981206018884971008854919922
                }
                if eq(index, 11) {
                    zero := 14271763308400718165336499097156975241954733520325982997864342600795471836726
                }
                if eq(index, 12) {
                    zero := 20066985985293572387227381049700832219069292839614107140851619262827735677018
                }
                if eq(index, 13) {
                    zero := 9394776414966240069580838672673694685292165040808226440647796406499139370960
                }
                if eq(index, 14) {
                    zero := 11331146992410411304059858900317123658895005918277453009197229807340014528524
                }
                if eq(index, 15) {
                    zero := 15819538789928229930262697811477882737253464456578333862691129291651619515538
                }
                if eq(index, 16) {
                    zero := 19217088683336594659449020493828377907203207941212636669271704950158751593251
                }
                if eq(index, 17) {
                    zero := 21035245323335827719745544373081896983162834604456827698288649288827293579666
                }
                if eq(index, 18) {
                    zero := 6939770416153240137322503476966641397417391950902474480970945462551409848591
                }
                if eq(index, 19) {
                    zero := 10941962436777715901943463195175331263348098796018438960955633645115732864202
                }
                if eq(index, 20) {
                    zero := 15019797232609675441998260052101280400536945603062888308240081994073687793470
                }
                if eq(index, 21) {
                    zero := 11702828337982203149177882813338547876343922920234831094975924378932809409969
                }
                if eq(index, 22) {
                    zero := 11217067736778784455593535811108456786943573747466706329920902520905755780395
                }
                if eq(index, 23) {
                    zero := 16072238744996205792852194127671441602062027943016727953216607508365787157389
                }
                if eq(index, 24) {
                    zero := 17681057402012993898104192736393849603097507831571622013521167331642182653248
                }
                if eq(index, 25) {
                    zero := 21694045479371014653083846597424257852691458318143380497809004364947786214945
                }
                if eq(index, 26) {
                    zero := 8163447297445169709687354538480474434591144168767135863541048304198280615192
                }
                if eq(index, 27) {
                    zero := 14081762237856300239452543304351251708585712948734528663957353575674639038357
                }
                if eq(index, 28) {
                    zero := 16619959921569409661790279042024627172199214148318086837362003702249041851090
                }
                if eq(index, 29) {
                    zero := 7022159125197495734384997711896547675021391130223237843255817587255104160365
                }
                if eq(index, 30) {
                    zero := 4114686047564160449611603615418567457008101555090703535405891656262658644463
                }
                if eq(index, 31) {
                    zero := 12549363297364877722388257367377629555213421373705596078299904496781819142130
                }
                if eq(index, 32) {
                    zero := 21443572485391568159800782191812935835534334817699172242223315142338162256601
                }
                __ret0 := zero
                leave
            }
            function internal_internal_lazyIndexForElement(level, index) -> __ret0 {
                __ret0 := add(mul(4294967295, level), index)
                leave
            }
            function internal_internal_lazyInsert(leaf) {
                let startIndex := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
                let maxIndex := and(shr(0, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
                if iszero(lt(leaf, 21888242871839275222246405745257275088548364400416034343698204186575808495617)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                        let __err_hash := keccak256(__err_ptr, 24)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(lt(startIndex, maxIndex)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                        let __err_hash := keccak256(__err_ptr, 24)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                {
                    let __compat_value := add(startIndex, 1)
                    let __compat_packed := and(__compat_value, 1099511627775)
                    let __compat_slot_word := sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)
                    let __compat_slot_cleared := and(__compat_slot_word, not(1208925819613529663078400))
                    sstore(97642014805756523509931909943000448576722218578626833372473198353469753044993, or(__compat_slot_cleared, shl(40, __compat_packed)))
                }
                let index := startIndex
                let hash := leaf
                let active := 1
                for {
                    let level := 0
                } lt(level, 32) {
                    level := add(level, 1)
                } {
                    if iszero(eq(active, 0)) {
                        let elementKey := internal_internal_lazyIndexForElement(level, index)
                        sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, elementKey), hash)
                        {
                            let __ite_cond := eq(and(index, 1), 0)
                            if __ite_cond {
                                active := 0
                            }
                            if iszero(__ite_cond) {
                                let siblingKey := internal_internal_lazyIndexForElement(level, sub(index, 1))
                                let sibling := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, siblingKey))
                                let parent := internal_internal_poseidon2(sibling, hash)
                                hash := parent
                                index := shr(1, index)
                            }
                        }
                    }
                }
                stop()
            }
            function internal_internal_lazyRootWithDepth32() -> __ret0 {
                let numberOfLeaves := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
                {
                    let __ite_cond := eq(numberOfLeaves, 0)
                    if __ite_cond {
                        __ret0 := 21443572485391568159800782191812935835534334817699172242223315142338162256601
                        leave
                    }
                    if iszero(__ite_cond) {
                        let levels_length := 33
                        let levels_data_offset := add(mload(64), 32)
                        mstore(sub(levels_data_offset, 32), levels_length)
                        mstore(64, add(levels_data_offset, mul(levels_length, 32)))
                        let index := sub(numberOfLeaves, 1)
                        {
                            let __ite_cond := eq(and(index, 1), 0)
                            if __ite_cond {
                                let elementKey := internal_internal_lazyIndexForElement(0, index)
                                let element := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, elementKey))
                                mstore(add(levels_data_offset, mul(0, 32)), element)
                            }
                            if iszero(__ite_cond) {
                                mstore(add(levels_data_offset, mul(0, 32)), 0)
                            }
                        }
                        for {
                            let level := 0
                        } lt(level, 32) {
                            level := add(level, 1)
                        } {
                            let current := __verity_array_element_memory_checked(levels_data_offset, levels_length, level)
                            {
                                let __ite_cond := eq(and(index, 1), 0)
                                if __ite_cond {
                                    let z := internal_internal_lazyDefaultZero(level)
                                    let parent := internal_internal_poseidon2(current, z)
                                    mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                                }
                                if iszero(__ite_cond) {
                                    let levelCount := shr(add(level, 1), numberOfLeaves)
                                    let parentIndex := shr(1, index)
                                    {
                                        let __ite_cond := gt(levelCount, parentIndex)
                                        if __ite_cond {
                                            let parentKey := internal_internal_lazyIndexForElement(add(level, 1), parentIndex)
                                            let parent := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, parentKey))
                                            mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                                        }
                                        if iszero(__ite_cond) {
                                            let siblingKey := internal_internal_lazyIndexForElement(level, sub(index, 1))
                                            let sibling := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, siblingKey))
                                            let parent := internal_internal_poseidon2(sibling, current)
                                            mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                                        }
                                    }
                                }
                            }
                            index := shr(1, index)
                        }
                        __ret0 := __verity_array_element_memory_checked(levels_data_offset, levels_length, 32)
                        leave
                    }
                }
            }
            function internal_internal_insertLeaves(leafHashes_data_offset, leafHashes_length) -> __ret0 {
                let count := leafHashes_length
                {
                    let __ite_cond := eq(count, 0)
                    if __ite_cond {
                        let currentRoot := sload(97642014805756523509931909943000448576722218578626833372473198353469753044992)
                        __ret0 := currentRoot
                        leave
                    }
                    if iszero(__ite_cond) {
                        for {
                            let m := 0
                        } lt(m, count) {
                            m := add(m, 1)
                        } {
                            let leaf := __verity_array_element_calldata_checked(leafHashes_data_offset, leafHashes_length, m)
                            internal_internal_lazyInsert(leaf)
                        }
                    }
                }
                let newRoot := internal_internal_lazyRootWithDepth32()
                sstore(97642014805756523509931909943000448576722218578626833372473198353469753044992, newRoot)
                sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044995, newRoot), 1)
                __ret0 := newRoot
                leave
            }
            function internal_internal_computeContextHash(ciphertexts_data_offset, ciphertexts_length) -> __ret0 {
                let cid := chainid()
                let selfAddr := address()
                {
                    let __ciphertextsHash_abi_array_ptr := mload(64)
                    mstore(__ciphertextsHash_abi_array_ptr, 32)
                    mstore(add(__ciphertextsHash_abi_array_ptr, 32), ciphertexts_length)
                    let __ciphertextsHash_abi_array_data_bytes := mul(ciphertexts_length, 128)
                    calldatacopy(add(__ciphertextsHash_abi_array_ptr, 64), ciphertexts_data_offset, __ciphertextsHash_abi_array_data_bytes)
                    let __ciphertextsHash_abi_array_total_bytes := add(64, __ciphertextsHash_abi_array_data_bytes)
                    let __ciphertextsHash_abi_array_padded_total := and(add(__ciphertextsHash_abi_array_total_bytes, 31), not(31))
                    mstore(64, add(__ciphertextsHash_abi_array_ptr, __ciphertextsHash_abi_array_padded_total))
                    let ciphertextsHash := keccak256(__ciphertextsHash_abi_array_ptr, __ciphertextsHash_abi_array_total_bytes)
                }
                {
                    let __packed_word_0 := cid
                    let __packed_word_1 := selfAddr
                    let __packed_word_2 := ciphertextsHash
                    mstore(0, __packed_word_0)
                    mstore(32, __packed_word_1)
                    mstore(64, __packed_word_2)
                }
                let rawContext := keccak256(0, 96)
                __ret0 := mod(rawContext, 21888242871839275222246405745257275088548364400416034343698204186575808495617)
                leave
            }
            function internal_internal_validateContext(merkleRoot, contextHash, expectedContext) {
                if iszero(eq(contextHash, expectedContext)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964436f6e746578744861736828290000000000000000)
                        let __err_hash := keccak256(__err_ptr, 24)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let rootSeen := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044995, merkleRoot))
                if iszero(iszero(eq(rootSeen, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644d65726b6c65526f6f742829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                stop()
            }
            function internal_internal_settleWithdrawalTransfer(token, recipient, amount) {
                let selfAddr := address()
                {
                    mstore(0, shl(224, 0x70a08231))
                    mstore(4, selfAddr)
                    let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                    if iszero(__balanceOf_success) {
                        let __balanceOf_rds := returndatasize()
                        returndatacopy(0, 0, __balanceOf_rds)
                        revert(0, __balanceOf_rds)
                    }
                    if iszero(eq(returndatasize(), 32)) {
                        revert(0, 0)
                    }
                }
                let poolBefore := mload(0)
                {
                    mstore(0, shl(224, 0x70a08231))
                    mstore(4, recipient)
                    let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                    if iszero(__balanceOf_success) {
                        let __balanceOf_rds := returndatasize()
                        returndatacopy(0, 0, __balanceOf_rds)
                        revert(0, __balanceOf_rds)
                    }
                    if iszero(eq(returndatasize(), 32)) {
                        revert(0, 0)
                    }
                }
                let recipientBefore := mload(0)
                {
                    mstore(0, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                    mstore(4, recipient)
                    mstore(36, amount)
                    let __st_success := call(gas(), token, 0, 0, 68, 0, 32)
                    if iszero(__st_success) {
                        mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                        mstore(4, 32)
                        mstore(36, 17)
                        mstore(68, 0x7472616e73666572207265766572746564000000000000000000000000000000)
                        revert(0, 100)
                    }
                    if eq(returndatasize(), 32) {
                        if iszero(mload(0)) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 23)
                            mstore(68, 0x7472616e736665722072657475726e65642066616c7365000000000000000000)
                            revert(0, 100)
                        }
                    }
                }
                {
                    mstore(0, shl(224, 0x70a08231))
                    mstore(4, selfAddr)
                    let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                    if iszero(__balanceOf_success) {
                        let __balanceOf_rds := returndatasize()
                        returndatacopy(0, 0, __balanceOf_rds)
                        revert(0, __balanceOf_rds)
                    }
                    if iszero(eq(returndatasize(), 32)) {
                        revert(0, 0)
                    }
                }
                let poolAfter := mload(0)
                {
                    mstore(0, shl(224, 0x70a08231))
                    mstore(4, recipient)
                    let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                    if iszero(__balanceOf_success) {
                        let __balanceOf_rds := returndatasize()
                        returndatacopy(0, 0, __balanceOf_rds)
                        revert(0, __balanceOf_rds)
                    }
                    if iszero(eq(returndatasize(), 32)) {
                        revert(0, 0)
                    }
                }
                let recipientAfter := mload(0)
                if iszero(eq(sub(poolBefore, poolAfter), amount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c576974686472617742616c616e63654d69736d617463682829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(sub(recipientAfter, recipientBefore), amount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c576974686472617742616c616e63654d69736d617463682829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                stop()
            }
            function internal_internal_transferWithBalanceCheck(permit_0_0, permit_0_1, permit_1, permit_2, depositor, signature_data_offset, signature_length, totalAmount, witness) {
                let selfAddr := address()
                let token := permit_0_0
                {
                    mstore(0, shl(224, 0x70a08231))
                    mstore(4, selfAddr)
                    let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                    if iszero(__balanceOf_success) {
                        let __balanceOf_rds := returndatasize()
                        returndatacopy(0, 0, __balanceOf_rds)
                        revert(0, __balanceOf_rds)
                    }
                    if iszero(eq(returndatasize(), 32)) {
                        revert(0, 0)
                    }
                }
                let balBefore := mload(0)
                let permitCallOk, permitAccepted := permitWitnessTransferFrom_try(sload(98021192859356073326120044313192698615125063568118942569962362705841075886849), token, permit_0_1, permit_1, permit_2, selfAddr, totalAmount, depositor, witness, signature_data_offset, signature_length)
                if iszero(permitCallOk) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                        let __err_hash := keccak256(__err_ptr, 28)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(permitAccepted) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                        let __err_hash := keccak256(__err_ptr, 28)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                {
                    mstore(0, shl(224, 0x70a08231))
                    mstore(4, selfAddr)
                    let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                    if iszero(__balanceOf_success) {
                        let __balanceOf_rds := returndatasize()
                        returndatacopy(0, 0, __balanceOf_rds)
                        revert(0, __balanceOf_rds)
                    }
                    if iszero(eq(returndatasize(), 32)) {
                        revert(0, 0)
                    }
                }
                let balAfter := mload(0)
                if iszero(eq(sub(balAfter, balBefore), totalAmount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                        let __err_hash := keccak256(__err_ptr, 28)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                stop()
            }
            function internal_internal_deposit(depositor, notes_data_offset, notes_length, ciphertexts_data_offset, ciphertexts_length, permit_0_0, permit_0_1, permit_1, permit_2, signature_data_offset, signature_length) {
                internal___modifier_onlyRelayer()
                let notesLen := notes_length
                if iszero(iszero(eq(notesLen, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c456d7074794e6f746573282900000000000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 16)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(ciphertexts_length, notesLen)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let newLeaves_length := notesLen
                let newLeaves_data_offset := add(mload(64), 32)
                mstore(sub(newLeaves_data_offset, 32), newLeaves_length)
                mstore(64, add(newLeaves_data_offset, mul(newLeaves_length, 32)))
                for {
                    let noteIndex := 0
                } lt(noteIndex, notesLen) {
                    noteIndex := add(noteIndex, 1)
                } {
                    let npk := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 0)
                    let token := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 1)
                    let amount := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 2)
                    internal_internal_validateNoteFields(npk, token, amount)
                    if iszero(eq(token, permit_0_0)) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c546f6b656e4d69736d61746368282900000000000000000000000000)
                            let __err_hash := keccak256(__err_ptr, 19)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    let leaf := internal_internal_hashNote(npk, token, amount)
                    mstore(add(newLeaves_data_offset, mul(noteIndex, 32)), leaf)
                }
                let totalAmount := internal_internal_sumNoteAmounts(notes_data_offset, notes_length)
                let selfAddr := address()
                {
                    let __notesHash_abi_two_arrays_ptr := mload(64)
                    let __notesHash_abi_array_a_data_bytes := mul(notesLen, 96)
                    let __notesHash_abi_array_b_data_bytes := mul(ciphertexts_length, 128)
                    let __notesHash_abi_array_a_tail_bytes := add(32, __notesHash_abi_array_a_data_bytes)
                    let __notesHash_abi_array_b_tail_bytes := add(32, __notesHash_abi_array_b_data_bytes)
                    let __notesHash_abi_array_b_head_offset := add(64, __notesHash_abi_array_a_tail_bytes)
                    let __notesHash_abi_two_arrays_total_bytes := add(__notesHash_abi_array_b_head_offset, __notesHash_abi_array_b_tail_bytes)
                    mstore(__notesHash_abi_two_arrays_ptr, 64)
                    mstore(add(__notesHash_abi_two_arrays_ptr, 32), __notesHash_abi_array_b_head_offset)
                    mstore(add(__notesHash_abi_two_arrays_ptr, 64), notesLen)
                    calldatacopy(add(__notesHash_abi_two_arrays_ptr, 96), notes_data_offset, __notesHash_abi_array_a_data_bytes)
                    mstore(add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_array_b_head_offset), ciphertexts_length)
                    calldatacopy(add(add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_array_b_head_offset), 32), ciphertexts_data_offset, __notesHash_abi_array_b_data_bytes)
                    let __notesHash_abi_two_arrays_padded_total := and(add(__notesHash_abi_two_arrays_total_bytes, 31), not(31))
                    mstore(64, add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_two_arrays_padded_total))
                    let notesHash := keccak256(__notesHash_abi_two_arrays_ptr, __notesHash_abi_two_arrays_total_bytes)
                }
                {
                    let __packed_word_0 := 85194627925618981451180140414236292804855281853588093248984713240396722975024
                    let __packed_word_1 := selfAddr
                    let __packed_word_2 := notesHash
                    mstore(0, __packed_word_0)
                    mstore(32, __packed_word_1)
                    mstore(64, __packed_word_2)
                }
                let witness := keccak256(0, 96)
                internal_internal_transferWithBalanceCheck(permit_0_0, permit_0_1, permit_1, permit_2, depositor, signature_data_offset, signature_length, totalAmount, witness)
                let startIndex := internal_internal_nextLeafIndex()
                let newRoot := internal_internal_insertLeaves(newLeaves_data_offset, newLeaves_length)
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x4465706f736974656428616464726573732c75696e743235362c75696e743235)
                    mstore(add(__evt_ptr, 32), 0x362c2875696e743235362c616464726573732c75696e74323536295b5d2c2875)
                    mstore(add(__evt_ptr, 64), 0x696e743235362c75696e743235365b335d295b5d290000000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 85)
                    let __evt_data_tail := 128
                    mstore(add(__evt_ptr, 0), newRoot)
                    mstore(add(__evt_ptr, 32), startIndex)
                    mstore(add(__evt_ptr, 64), __evt_data_tail)
                    let __evt_arg2_len := notes_length
                    let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                    mstore(__evt_arg2_dst, __evt_arg2_len)
                    let __evt_arg2_byte_len := mul(__evt_arg2_len, 96)
                    for {
                        let __evt_arg2_i := 0
                    } lt(__evt_arg2_i, __evt_arg2_len) {
                        __evt_arg2_i := add(__evt_arg2_i, 1)
                    } {
                        let __evt_arg2_elem_base := add(add(4, notes_offset), mul(__evt_arg2_i, 96))
                        let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 96))
                        mstore(add(__evt_arg2_out_base, 0), calldataload(add(__evt_arg2_elem_base, 0)))
                        mstore(add(__evt_arg2_out_base, 32), and(calldataload(add(__evt_arg2_elem_base, 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                        mstore(add(__evt_arg2_out_base, 64), calldataload(add(__evt_arg2_elem_base, 64)))
                    }
                    let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                    mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                    mstore(add(__evt_ptr, 96), __evt_data_tail)
                    let __evt_arg3_len := ciphertexts_length
                    let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                    mstore(__evt_arg3_dst, __evt_arg3_len)
                    let __evt_arg3_byte_len := mul(__evt_arg3_len, 128)
                    for {
                        let __evt_arg3_i := 0
                    } lt(__evt_arg3_i, __evt_arg3_len) {
                        __evt_arg3_i := add(__evt_arg3_i, 1)
                    } {
                        let __evt_arg3_elem_base := add(add(4, ciphertexts_offset), mul(__evt_arg3_i, 128))
                        let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 128))
                        mstore(add(__evt_arg3_out_base, 0), calldataload(add(__evt_arg3_elem_base, 0)))
                        mstore(add(__evt_arg3_out_base, 32), calldataload(add(__evt_arg3_elem_base, 32)))
                        mstore(add(__evt_arg3_out_base, 64), calldataload(add(__evt_arg3_elem_base, 64)))
                        mstore(add(__evt_arg3_out_base, 96), calldataload(add(__evt_arg3_elem_base, 96)))
                    }
                    let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                    mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                    log2(__evt_ptr, __evt_data_tail, __evt_topic0, and(depositor, 0xffffffffffffffffffffffffffffffffffffffff))
                }
                stop()
            }
            function internal_internal_transfer(transactions_data_offset, transactions_length) {
                internal___modifier_onlyRelayer()
                let txLen := transactions_length
                if iszero(iszero(eq(txLen, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                for {
                    let i := 0
                } lt(i, txLen) {
                    i := add(i, 1)
                } {
                    let verifierRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
                    let success, circuit_verifier, circuit_inputCount, circuit_outputCount, circuit_active := getCircuit_try(verifierRouter, __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 8))
                    if iszero(success) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                            let __err_hash := keccak256(__err_ptr, 26)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    if iszero(iszero(eq(circuit_verifier, 0))) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                            let __err_hash := keccak256(__err_ptr, 26)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    if iszero(iszero(eq(circuit_active, 0))) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c43697263756974496e61637469766528290000000000000000000000)
                            let __err_hash := keccak256(__err_ptr, 21)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10), circuit_inputCount)) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964496e70757453686170652829000000000000000000)
                            let __err_hash := keccak256(__err_ptr, 23)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11), circuit_outputCount)) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                            let __err_hash := keccak256(__err_ptr, 24)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    let ciphertextCount := internal_internal_countNonZero(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 11), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
                    if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13), ciphertextCount)) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                            let __err_hash := keccak256(__err_ptr, 29)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    let computedContext := internal_internal_computeContextHash(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 13), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13))
                    internal_internal_validateContext(__verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 9), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 12), computedContext)
                    let proofOk, ok := verifySpend_try(circuit_verifier, __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 0), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 1), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 2), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 3), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 4), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 5), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 6), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 7), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 9), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 12), __verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 11), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11))
                    if iszero(proofOk) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                            let __err_hash := keccak256(__err_ptr, 29)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    if iszero(ok) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                            let __err_hash := keccak256(__err_ptr, 29)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    internal_internal_spendNullifiers(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10))
                    let leavesCount := 0
                    for {
                        let commitCountIndex := 0
                    } lt(commitCountIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11)) {
                        commitCountIndex := add(commitCountIndex, 1)
                    } {
                        let commitment := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 11, commitCountIndex)
                        if iszero(eq(commitment, 0)) {
                            leavesCount := add(leavesCount, 1)
                        }
                    }
                    let leaves_length := leavesCount
                    let leaves_data_offset := add(mload(64), 32)
                    mstore(sub(leaves_data_offset, 32), leaves_length)
                    mstore(64, add(leaves_data_offset, mul(leaves_length, 32)))
                    let leafWriteIndex := 0
                    for {
                        let commitWriteIndex := 0
                    } lt(commitWriteIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11)) {
                        commitWriteIndex := add(commitWriteIndex, 1)
                    } {
                        let commitment := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 11, commitWriteIndex)
                        if iszero(eq(commitment, 0)) {
                            mstore(add(leaves_data_offset, mul(leafWriteIndex, 32)), commitment)
                            leafWriteIndex := add(leafWriteIndex, 1)
                        }
                    }
                    let nullifierCount := 0
                    for {
                        let nullifierCountIndex := 0
                    } lt(nullifierCountIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10)) {
                        nullifierCountIndex := add(nullifierCountIndex, 1)
                    } {
                        let nullifierHash := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 10, nullifierCountIndex)
                        if iszero(eq(nullifierHash, 0)) {
                            nullifierCount := add(nullifierCount, 1)
                        }
                    }
                    let realNulls_length := nullifierCount
                    let realNulls_data_offset := add(mload(64), 32)
                    mstore(sub(realNulls_data_offset, 32), realNulls_length)
                    mstore(64, add(realNulls_data_offset, mul(realNulls_length, 32)))
                    let nullifierWriteIndex := 0
                    for {
                        let nullifierWriteIndexLoop := 0
                    } lt(nullifierWriteIndexLoop, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10)) {
                        nullifierWriteIndexLoop := add(nullifierWriteIndexLoop, 1)
                    } {
                        let nullifierHash := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 10, nullifierWriteIndexLoop)
                        if iszero(eq(nullifierHash, 0)) {
                            mstore(add(realNulls_data_offset, mul(nullifierWriteIndex, 32)), nullifierHash)
                            nullifierWriteIndex := add(nullifierWriteIndex, 1)
                        }
                    }
                    let startIndex := internal_internal_nextLeafIndex()
                    let newRoot := internal_internal_insertLeaves(leaves_data_offset, leaves_length)
                    {
                        let __evt_ptr := mload(64)
                        mstore(add(__evt_ptr, 0), 0x5472616e736665727265642875696e743235362c75696e743235362c75696e74)
                        mstore(add(__evt_ptr, 32), 0x3235365b5d2c75696e743235365b5d2c2875696e743235362c75696e74323536)
                        mstore(add(__evt_ptr, 64), 0x5b335d295b5d2900000000000000000000000000000000000000000000000000)
                        let __evt_topic0 := keccak256(__evt_ptr, 71)
                        let __evt_data_tail := 128
                        mstore(add(__evt_ptr, 0), startIndex)
                        mstore(add(__evt_ptr, 32), __evt_data_tail)
                        let __evt_arg1_len := leaves_length
                        let __evt_arg1_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg1_dst, __evt_arg1_len)
                        let __evt_arg1_byte_len := mul(__evt_arg1_len, 32)
                        for {
                            let __evt_arg1_i := 0
                        } lt(__evt_arg1_i, __evt_arg1_len) {
                            __evt_arg1_i := add(__evt_arg1_i, 1)
                        } {
                            let __evt_arg1_elem_base := add(leaves_data_offset, mul(__evt_arg1_i, 32))
                            let __evt_arg1_out_base := add(add(__evt_arg1_dst, 32), mul(__evt_arg1_i, 32))
                            mstore(add(__evt_arg1_out_base, 0), mload(add(__evt_arg1_elem_base, 0)))
                        }
                        let __evt_arg1_padded := and(add(__evt_arg1_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg1_dst, 32), __evt_arg1_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg1_padded))
                        mstore(add(__evt_ptr, 64), __evt_data_tail)
                        let __evt_arg2_len := realNulls_length
                        let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg2_dst, __evt_arg2_len)
                        let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                        for {
                            let __evt_arg2_i := 0
                        } lt(__evt_arg2_i, __evt_arg2_len) {
                            __evt_arg2_i := add(__evt_arg2_i, 1)
                        } {
                            let __evt_arg2_elem_base := add(realNulls_data_offset, mul(__evt_arg2_i, 32))
                            let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                            mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                        }
                        let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                        mstore(add(__evt_ptr, 96), __evt_data_tail)
                        let __evt_arg3_len := __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13)
                        let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                        mstore(__evt_arg3_dst, __evt_arg3_len)
                        let __evt_arg3_byte_len := mul(__evt_arg3_len, 128)
                        for {
                            let __evt_arg3_i := 0
                        } lt(__evt_arg3_i, __evt_arg3_len) {
                            __evt_arg3_i := add(__evt_arg3_i, 1)
                        } {
                            let __evt_arg3_elem_base := add(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 13), mul(__evt_arg3_i, 128))
                            let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 128))
                            mstore(add(__evt_arg3_out_base, 0), calldataload(add(__evt_arg3_elem_base, 0)))
                            mstore(add(__evt_arg3_out_base, 32), calldataload(add(__evt_arg3_elem_base, 32)))
                            mstore(add(__evt_arg3_out_base, 64), calldataload(add(__evt_arg3_elem_base, 64)))
                            mstore(add(__evt_arg3_out_base, 96), calldataload(add(__evt_arg3_elem_base, 96)))
                        }
                        let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                        mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                        __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                        log2(__evt_ptr, __evt_data_tail, __evt_topic0, newRoot)
                    }
                }
                stop()
            }
            function internal_internal_executeWithdrawal(txn_data_offset, emergency) {
                if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15), 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465416d6f756e742829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f74654e504b2829000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 20)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465546f6b656e282900000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 22)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if gt(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), 1461501637330902918203684832716283019655932542975) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c526563697069656e742829)
                        let __err_hash := keccak256(__err_ptr, 32)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let recipient := __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13)
                let selfAddr := address()
                if iszero(iszero(eq(recipient, selfAddr))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c526563697069656e742829)
                        let __err_hash := keccak256(__err_ptr, 32)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let verifierRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
                let success, circuit_verifier, circuit_inputCount, circuit_outputCount, circuit_active := getCircuit_try(verifierRouter, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 8))
                if iszero(success) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                        let __err_hash := keccak256(__err_ptr, 26)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(circuit_verifier, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                        let __err_hash := keccak256(__err_ptr, 26)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(circuit_active, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c43697263756974496e61637469766528290000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 21)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10), circuit_inputCount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964496e70757453686170652829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11), circuit_outputCount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                        let __err_hash := keccak256(__err_ptr, 24)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let wSlot := sub(circuit_outputCount, 1)
                let withdrawalCommitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, wSlot)
                if iszero(iszero(eq(withdrawalCommitment, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c5769746864726177616c536c6f745a65726f28290000000000000000)
                        let __err_hash := keccak256(__err_ptr, 24)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let noteHash := internal_internal_hashNote(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15))
                if iszero(eq(withdrawalCommitment, noteHash)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c436f6d6d69746d656e7428)
                        mstore(add(__err_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 33)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let ciphertextCount := internal_internal_countNonZero(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 11), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11), wSlot)
                if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16), ciphertextCount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let computedContext := internal_internal_computeContextHash(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16))
                internal_internal_validateContext(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 9), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 12), computedContext)
                let proofOk, ok := verifySpend_try(circuit_verifier, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 0), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 1), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 2), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 3), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 4), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 5), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 6), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 7), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 9), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 12), __verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 11), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11))
                if iszero(proofOk) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(ok) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                        let __err_hash := keccak256(__err_ptr, 29)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                internal_internal_spendNullifiers(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10))
                let leavesCount := 0
                for {
                    let withdrawCommitCountIndex := 0
                } lt(withdrawCommitCountIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11)) {
                    withdrawCommitCountIndex := add(withdrawCommitCountIndex, 1)
                } {
                    let commitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, withdrawCommitCountIndex)
                    if iszero(eq(withdrawCommitCountIndex, wSlot)) {
                        if iszero(eq(commitment, 0)) {
                            leavesCount := add(leavesCount, 1)
                        }
                    }
                }
                let leaves_length := leavesCount
                let leaves_data_offset := add(mload(64), 32)
                mstore(sub(leaves_data_offset, 32), leaves_length)
                mstore(64, add(leaves_data_offset, mul(leaves_length, 32)))
                let leafWriteIndex := 0
                for {
                    let withdrawCommitWriteIndex := 0
                } lt(withdrawCommitWriteIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11)) {
                    withdrawCommitWriteIndex := add(withdrawCommitWriteIndex, 1)
                } {
                    let commitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, withdrawCommitWriteIndex)
                    if iszero(eq(withdrawCommitWriteIndex, wSlot)) {
                        if iszero(eq(commitment, 0)) {
                            mstore(add(leaves_data_offset, mul(leafWriteIndex, 32)), commitment)
                            leafWriteIndex := add(leafWriteIndex, 1)
                        }
                    }
                }
                let nullifierCount := 0
                for {
                    let withdrawNullifierCountIndex := 0
                } lt(withdrawNullifierCountIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10)) {
                    withdrawNullifierCountIndex := add(withdrawNullifierCountIndex, 1)
                } {
                    let nullifierHash := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 10, withdrawNullifierCountIndex)
                    if iszero(eq(nullifierHash, 0)) {
                        nullifierCount := add(nullifierCount, 1)
                    }
                }
                let realNulls_length := nullifierCount
                let realNulls_data_offset := add(mload(64), 32)
                mstore(sub(realNulls_data_offset, 32), realNulls_length)
                mstore(64, add(realNulls_data_offset, mul(realNulls_length, 32)))
                let nullifierWriteIndex := 0
                for {
                    let withdrawNullifierWriteIndexLoop := 0
                } lt(withdrawNullifierWriteIndexLoop, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10)) {
                    withdrawNullifierWriteIndexLoop := add(withdrawNullifierWriteIndexLoop, 1)
                } {
                    let nullifierHash := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 10, withdrawNullifierWriteIndexLoop)
                    if iszero(eq(nullifierHash, 0)) {
                        mstore(add(realNulls_data_offset, mul(nullifierWriteIndex, 32)), nullifierHash)
                        nullifierWriteIndex := add(nullifierWriteIndex, 1)
                    }
                }
                let startIndex := internal_internal_nextLeafIndex()
                let newRoot := internal_internal_insertLeaves(leaves_data_offset, leaves_length)
                internal_internal_settleWithdrawalTransfer(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), recipient, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15))
                {
                    let __ite_cond := emergency
                    if __ite_cond {
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x456d657267656e637957697468647261776e28616464726573732c2875696e74)
                            mstore(add(__evt_ptr, 32), 0x3235362c616464726573732c75696e74323536292c75696e743235362c75696e)
                            mstore(add(__evt_ptr, 64), 0x743235362c75696e743235365b5d2c75696e743235365b5d2c2875696e743235)
                            mstore(add(__evt_ptr, 96), 0x362c75696e743235365b335d295b5d2900000000000000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 112)
                            let __evt_data_tail := 224
                            mstore(add(add(__evt_ptr, 0), 0), calldataload(add(add(txn_data_offset, 416), 0)))
                            mstore(add(add(__evt_ptr, 0), 32), and(calldataload(add(add(txn_data_offset, 416), 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(add(add(__evt_ptr, 0), 64), calldataload(add(add(txn_data_offset, 416), 64)))
                            mstore(add(__evt_ptr, 96), startIndex)
                            mstore(add(__evt_ptr, 128), __evt_data_tail)
                            let __evt_arg2_len := leaves_length
                            let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                            mstore(__evt_arg2_dst, __evt_arg2_len)
                            let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                            for {
                                let __evt_arg2_i := 0
                            } lt(__evt_arg2_i, __evt_arg2_len) {
                                __evt_arg2_i := add(__evt_arg2_i, 1)
                            } {
                                let __evt_arg2_elem_base := add(leaves_data_offset, mul(__evt_arg2_i, 32))
                                let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                                mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                            }
                            let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                            mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                            __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                            mstore(add(__evt_ptr, 160), __evt_data_tail)
                            let __evt_arg3_len := realNulls_length
                            let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                            mstore(__evt_arg3_dst, __evt_arg3_len)
                            let __evt_arg3_byte_len := mul(__evt_arg3_len, 32)
                            for {
                                let __evt_arg3_i := 0
                            } lt(__evt_arg3_i, __evt_arg3_len) {
                                __evt_arg3_i := add(__evt_arg3_i, 1)
                            } {
                                let __evt_arg3_elem_base := add(realNulls_data_offset, mul(__evt_arg3_i, 32))
                                let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 32))
                                mstore(add(__evt_arg3_out_base, 0), mload(add(__evt_arg3_elem_base, 0)))
                            }
                            let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                            mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                            __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                            mstore(add(__evt_ptr, 192), __evt_data_tail)
                            let __evt_arg4_len := __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16)
                            let __evt_arg4_dst := add(__evt_ptr, __evt_data_tail)
                            mstore(__evt_arg4_dst, __evt_arg4_len)
                            let __evt_arg4_byte_len := mul(__evt_arg4_len, 128)
                            for {
                                let __evt_arg4_i := 0
                            } lt(__evt_arg4_i, __evt_arg4_len) {
                                __evt_arg4_i := add(__evt_arg4_i, 1)
                            } {
                                let __evt_arg4_elem_base := add(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), mul(__evt_arg4_i, 128))
                                let __evt_arg4_out_base := add(add(__evt_arg4_dst, 32), mul(__evt_arg4_i, 128))
                                mstore(add(__evt_arg4_out_base, 0), calldataload(add(__evt_arg4_elem_base, 0)))
                                mstore(add(__evt_arg4_out_base, 32), calldataload(add(__evt_arg4_elem_base, 32)))
                                mstore(add(__evt_arg4_out_base, 64), calldataload(add(__evt_arg4_elem_base, 64)))
                                mstore(add(__evt_arg4_out_base, 96), calldataload(add(__evt_arg4_elem_base, 96)))
                            }
                            let __evt_arg4_padded := and(add(__evt_arg4_byte_len, 31), not(31))
                            mstore(add(add(__evt_arg4_dst, 32), __evt_arg4_byte_len), 0)
                            __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg4_padded))
                            log3(__evt_ptr, __evt_data_tail, __evt_topic0, and(recipient, 0xffffffffffffffffffffffffffffffffffffffff), newRoot)
                        }
                    }
                    if iszero(__ite_cond) {
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x57697468647261776e28616464726573732c2875696e743235362c6164647265)
                            mstore(add(__evt_ptr, 32), 0x73732c75696e74323536292c75696e743235362c75696e743235362c75696e74)
                            mstore(add(__evt_ptr, 64), 0x3235365b5d2c75696e743235365b5d2c2875696e743235362c75696e74323536)
                            mstore(add(__evt_ptr, 96), 0x5b335d295b5d2900000000000000000000000000000000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 103)
                            let __evt_data_tail := 224
                            mstore(add(add(__evt_ptr, 0), 0), calldataload(add(add(txn_data_offset, 416), 0)))
                            mstore(add(add(__evt_ptr, 0), 32), and(calldataload(add(add(txn_data_offset, 416), 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(add(add(__evt_ptr, 0), 64), calldataload(add(add(txn_data_offset, 416), 64)))
                            mstore(add(__evt_ptr, 96), startIndex)
                            mstore(add(__evt_ptr, 128), __evt_data_tail)
                            let __evt_arg2_len := leaves_length
                            let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                            mstore(__evt_arg2_dst, __evt_arg2_len)
                            let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                            for {
                                let __evt_arg2_i := 0
                            } lt(__evt_arg2_i, __evt_arg2_len) {
                                __evt_arg2_i := add(__evt_arg2_i, 1)
                            } {
                                let __evt_arg2_elem_base := add(leaves_data_offset, mul(__evt_arg2_i, 32))
                                let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                                mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                            }
                            let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                            mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                            __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                            mstore(add(__evt_ptr, 160), __evt_data_tail)
                            let __evt_arg3_len := realNulls_length
                            let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                            mstore(__evt_arg3_dst, __evt_arg3_len)
                            let __evt_arg3_byte_len := mul(__evt_arg3_len, 32)
                            for {
                                let __evt_arg3_i := 0
                            } lt(__evt_arg3_i, __evt_arg3_len) {
                                __evt_arg3_i := add(__evt_arg3_i, 1)
                            } {
                                let __evt_arg3_elem_base := add(realNulls_data_offset, mul(__evt_arg3_i, 32))
                                let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 32))
                                mstore(add(__evt_arg3_out_base, 0), mload(add(__evt_arg3_elem_base, 0)))
                            }
                            let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                            mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                            __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                            mstore(add(__evt_ptr, 192), __evt_data_tail)
                            let __evt_arg4_len := __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16)
                            let __evt_arg4_dst := add(__evt_ptr, __evt_data_tail)
                            mstore(__evt_arg4_dst, __evt_arg4_len)
                            let __evt_arg4_byte_len := mul(__evt_arg4_len, 128)
                            for {
                                let __evt_arg4_i := 0
                            } lt(__evt_arg4_i, __evt_arg4_len) {
                                __evt_arg4_i := add(__evt_arg4_i, 1)
                            } {
                                let __evt_arg4_elem_base := add(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), mul(__evt_arg4_i, 128))
                                let __evt_arg4_out_base := add(add(__evt_arg4_dst, 32), mul(__evt_arg4_i, 128))
                                mstore(add(__evt_arg4_out_base, 0), calldataload(add(__evt_arg4_elem_base, 0)))
                                mstore(add(__evt_arg4_out_base, 32), calldataload(add(__evt_arg4_elem_base, 32)))
                                mstore(add(__evt_arg4_out_base, 64), calldataload(add(__evt_arg4_elem_base, 64)))
                                mstore(add(__evt_arg4_out_base, 96), calldataload(add(__evt_arg4_elem_base, 96)))
                            }
                            let __evt_arg4_padded := and(add(__evt_arg4_byte_len, 31), not(31))
                            mstore(add(add(__evt_arg4_dst, 32), __evt_arg4_byte_len), 0)
                            __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg4_padded))
                            log3(__evt_ptr, __evt_data_tail, __evt_topic0, and(recipient, 0xffffffffffffffffffffffffffffffffffffffff), newRoot)
                        }
                    }
                }
                stop()
            }
            function internal_internal_withdraw(transactions_data_offset, transactions_length) {
                internal___modifier_onlyRelayer()
                let txLen := transactions_length
                if iszero(iszero(eq(txLen, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                for {
                    let i := 0
                } lt(i, txLen) {
                    i := add(i, 1)
                } {
                    internal_internal_executeWithdrawal(__verity_array_element_dynamic_data_offset_calldata_checked(transactions_data_offset, transactions_length, i), 0)
                }
                stop()
            }
            function internal_internal_emergencyWithdraw(transactions_data_offset, transactions_length) {
                let txLen := transactions_length
                if iszero(iszero(eq(txLen, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 23)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                for {
                    let i := 0
                } lt(i, txLen) {
                    i := add(i, 1)
                } {
                    internal_internal_executeWithdrawal(__verity_array_element_dynamic_data_offset_calldata_checked(transactions_data_offset, transactions_length, i), 1)
                }
                stop()
            }
            function internal___modifier_onlyRelayer() {
                let sender := caller()
                let isR := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, sender))
                if iszero(iszero(eq(isR, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x506f6f6c556e617574686f72697a656452656c61796572282900000000000000)
                        let __err_hash := keccak256(__err_ptr, 25)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                stop()
            }
            {
                let __has_selector := iszero(lt(calldatasize(), 4))
                if iszero(__has_selector) {
                    revert(0, 0)
                }
                if __has_selector {
                    switch shr(224, calldataload(0))
                    case 0xc0c53b8b {
                        /* initialize() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        let verifierRouter := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let ownerAddr := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                        let relayer := and(calldataload(68), 0xffffffffffffffffffffffffffffffffffffffff)
                        if iszero(eq(sload(0), 0)) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 23)
                            mstore(68, 0x696e697469616c697a657220616c72656164792072756e000000000000000000)
                            revert(0, 100)
                        }
                        sstore(0, 1)
                        let qMinusG1Y := 21888242871839275222246405745257275088696311157297823662689037894645226208581
                        let g2x1 := 11559732032986387107991004021392285783925812861821192530917403151452391805634
                        let g2x2 := 10857046999023057135944570762232829481370756359578518086990519993285655852781
                        let g2y1 := 4082367875863433681332203403145435568316851327593401208105741076214120093531
                        let g2y2 := 8495653923123431417604973247489272438418190587263600148770280649306958101930
                        mstore(0, 1)
                        mstore(32, 2)
                        mstore(64, g2x1)
                        mstore(96, g2x2)
                        mstore(128, g2y1)
                        mstore(160, g2y2)
                        mstore(192, 1)
                        mstore(224, qMinusG1Y)
                        mstore(256, g2x1)
                        mstore(288, g2x2)
                        mstore(320, g2y1)
                        mstore(352, g2y2)
                        let pairA := 0
                        {
                            let __bn256_pairing_output_offset := 0
                            let __bn256_pairing_success := staticcall(gas(), 8, 0, 384, __bn256_pairing_output_offset, 32)
                            if iszero(__bn256_pairing_success) {
                                revert(0, 0)
                            }
                            pairA := mload(__bn256_pairing_output_offset)
                        }
                        if iszero(eq(pairA, 1)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        mstore(0, 1)
                        mstore(32, 2)
                        let pairB := 0
                        {
                            let __bn256_pairing_output_offset := 0
                            let __bn256_pairing_success := staticcall(gas(), 8, 0, 192, __bn256_pairing_output_offset, 32)
                            if iszero(__bn256_pairing_success) {
                                revert(0, 0)
                            }
                            pairB := mload(__bn256_pairing_output_offset)
                        }
                        if iszero(eq(pairB, 0)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let twoG1x := 1368015179489954701390400359078579693043519447331113978918064868415326638035
                        let twoG1y := 9918110051302171585080402603319702774565515993150576347155970296011118125764
                        let mul2x := 0
                        let mul2y := 0
                        {
                            mstore(0, 1)
                            mstore(32, 2)
                            mstore(64, 2)
                            let __bn256_mul_success := staticcall(gas(), 7, 0, 96, 0, 64)
                            if iszero(__bn256_mul_success) {
                                revert(0, 0)
                            }
                            mul2x := mload(0)
                            mul2y := mload(32)
                        }
                        if iszero(eq(mul2x, twoG1x)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(eq(mul2y, twoG1y)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let mul3x := 0
                        let mul3y := 0
                        {
                            mstore(0, 1)
                            mstore(32, 2)
                            mstore(64, 3)
                            let __bn256_mul_success := staticcall(gas(), 7, 0, 96, 0, 64)
                            if iszero(__bn256_mul_success) {
                                revert(0, 0)
                            }
                            mul3x := mload(0)
                            mul3y := mload(32)
                        }
                        if iszero(or(iszero(iszero(iszero(eq(mul3x, twoG1x)))), iszero(iszero(iszero(eq(mul3y, twoG1y)))))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let add2x := 0
                        let add2y := 0
                        {
                            mstore(0, 1)
                            mstore(32, 2)
                            mstore(64, 1)
                            mstore(96, 2)
                            let __bn256_add_success := staticcall(gas(), 6, 0, 128, 0, 64)
                            if iszero(__bn256_add_success) {
                                revert(0, 0)
                            }
                            add2x := mload(0)
                            add2y := mload(32)
                        }
                        if iszero(eq(add2x, twoG1x)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(eq(add2y, twoG1y)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let add3x := 0
                        let add3y := 0
                        {
                            mstore(0, 1)
                            mstore(32, 2)
                            mstore(64, twoG1x)
                            mstore(96, twoG1y)
                            let __bn256_add_success := staticcall(gas(), 6, 0, 128, 0, 64)
                            if iszero(__bn256_add_success) {
                                revert(0, 0)
                            }
                            add3x := mload(0)
                            add3y := mload(32)
                        }
                        if iszero(or(iszero(iszero(iszero(eq(add3x, twoG1x)))), iszero(iszero(iszero(eq(add3y, twoG1y)))))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(eq(mul3x, add3x)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(eq(mul3y, add3y)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c507265636f6d70696c65556e617661696c61626c6528290000000000)
                                let __err_hash := keccak256(__err_ptr, 27)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        sstore(1, and(ownerAddr, 0xffffffffffffffffffffffffffffffffffffffff))
                        sstore(2, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
                        if iszero(iszero(eq(verifierRouter, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 19)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        sstore(97642014805756523509931909943000448576722218578626833372473198353469753044997, and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
                        if iszero(iszero(eq(relayer, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 19)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let already := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
                        if iszero(eq(already, 0)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c52656c61796572416c72656164794163746976652829000000000000)
                                let __err_hash := keccak256(__err_ptr, 26)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 1)
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x52656c6179657241646465642861646472657373290000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 21)
                            log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
                        }
                        stop()
                    }
                    case 0xfe060733 {
                        /* authorizeUpgrade() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let _newImplementation := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        if iszero(eq(caller(), sload(1))) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 38)
                            mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                            mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                            revert(0, 132)
                        }
                        stop()
                    }
                    case 0x715018a6 {
                        /* renounceOwnership() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        if iszero(eq(caller(), sload(1))) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 38)
                            mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                            mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                            revert(0, 132)
                        }
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x506f6f6c52656e6f756e63654f776e65727368697044697361626c6564282900)
                            let __err_hash := keccak256(__err_ptr, 31)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                        stop()
                    }
                    case 0x541d5548 {
                        /* isRelayer() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let account := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let r := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, account))
                        mstore(0, r)
                        return(0, 32)
                    }
                    case 0x0be4f422 {
                        /* nextLeafIndex() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        let n := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
                        mstore(0, n)
                        return(0, 32)
                    }
                    case 0xe7d22434 {
                        /* hashNote() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        let npk := calldataload(4)
                        let _token := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                        let amount := calldataload(68)
                        mstore(0, poseidonT4(npk, _token, amount))
                        return(0, 32)
                    }
                    case 0x6e9c433b {
                        /* poseidon2() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let lhs := calldataload(4)
                        let rhs := calldataload(36)
                        mstore(0, poseidonT3(lhs, rhs))
                        return(0, 32)
                    }
                    case 0x2b0163d7 {
                        /* validateNoteFields() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        let npk := calldataload(4)
                        let token := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                        let amount := calldataload(68)
                        if iszero(iszero(eq(token, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465546f6b656e282900000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 22)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(and(iszero(iszero(iszero(eq(amount, 0)))), iszero(iszero(iszero(gt(amount, 100000000000000000000000000000000000000000000000000000000000000000000)))))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465416d6f756e742829000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 23)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(and(iszero(iszero(iszero(eq(npk, 0)))), iszero(iszero(lt(npk, 21888242871839275222246405745257275088548364400416034343698204186575808495617))))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f74654e504b2829000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 20)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        stop()
                    }
                    case 0x95aa5406 {
                        /* sumNoteAmounts() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let notes_offset := calldataload(4)
                        if lt(notes_offset, 32) {
                            revert(0, 0)
                        }
                        let notes_abs_offset := add(4, notes_offset)
                        if gt(notes_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let notes_length := calldataload(notes_abs_offset)
                        let notes_tail_head_end := add(notes_abs_offset, 32)
                        let notes_tail_remaining := sub(calldatasize(), notes_tail_head_end)
                        if gt(notes_length, div(notes_tail_remaining, 96)) {
                            revert(0, 0)
                        }
                        let notes_data_offset := notes_tail_head_end
                        let totalAmount := 0
                        for {
                            let i := 0
                        } lt(i, notes_length) {
                            i := add(i, 1)
                        } {
                            let amount := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, i, 3, 2)
                            totalAmount := add(totalAmount, amount)
                        }
                        mstore(0, totalAmount)
                        return(0, 32)
                    }
                    case 0xde410d85 {
                        /* validateAndCollectDeposit() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let notes_offset := calldataload(4)
                        if lt(notes_offset, 64) {
                            revert(0, 0)
                        }
                        let notes_abs_offset := add(4, notes_offset)
                        if gt(notes_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let notes_length := calldataload(notes_abs_offset)
                        let notes_tail_head_end := add(notes_abs_offset, 32)
                        let notes_tail_remaining := sub(calldatasize(), notes_tail_head_end)
                        if gt(notes_length, div(notes_tail_remaining, 96)) {
                            revert(0, 0)
                        }
                        let notes_data_offset := notes_tail_head_end
                        let permitToken := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                        let notesLen := notes_length
                        let newLeaves_length := notesLen
                        let newLeaves_data_offset := add(mload(64), 32)
                        mstore(sub(newLeaves_data_offset, 32), newLeaves_length)
                        mstore(64, add(newLeaves_data_offset, mul(newLeaves_length, 32)))
                        for {
                            let i := 0
                        } lt(i, notesLen) {
                            i := add(i, 1)
                        } {
                            let npk := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, i, 3, 0)
                            let token := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, i, 3, 1)
                            let amount := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, i, 3, 2)
                            internal_internal_validateNoteFields(npk, token, amount)
                            if iszero(eq(token, permitToken)) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c546f6b656e4d69736d61746368282900000000000000000000000000)
                                    let __err_hash := keccak256(__err_ptr, 19)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            let leaf := internal_internal_hashNote(npk, token, amount)
                            mstore(add(newLeaves_data_offset, mul(i, 32)), leaf)
                        }
                        mstore(0, 32)
                        mstore(32, newLeaves_length)
                        calldatacopy(64, newLeaves_data_offset, mul(newLeaves_length, 32))
                        return(0, add(64, mul(newLeaves_length, 32)))
                    }
                    case 0xdd39f00d {
                        /* addRelayer() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let relayer := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        if iszero(eq(caller(), sload(1))) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 38)
                            mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                            mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                            revert(0, 132)
                        }
                        if iszero(iszero(eq(relayer, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 19)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let already := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
                        if iszero(eq(already, 0)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c52656c61796572416c72656164794163746976652829000000000000)
                                let __err_hash := keccak256(__err_ptr, 26)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 1)
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x52656c6179657241646465642861646472657373290000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 21)
                            log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
                        }
                        stop()
                    }
                    case 0x60f0a5ac {
                        /* removeRelayer() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let relayer := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        if iszero(eq(caller(), sload(1))) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 38)
                            mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                            mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                            revert(0, 132)
                        }
                        if iszero(iszero(eq(relayer, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 19)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let active := sload(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer))
                        if iszero(iszero(eq(active, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c556e617574686f72697a656452656c61796572282900000000000000)
                                let __err_hash := keccak256(__err_ptr, 25)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        sstore(mappingSlot(98021192859356073326120044313192698615125063568118942569962362705841075886848, relayer), 0)
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x52656c6179657252656d6f766564286164647265737329000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 23)
                            log2(__evt_ptr, 0, __evt_topic0, and(relayer, 0xffffffffffffffffffffffffffffffffffffffff))
                        }
                        stop()
                    }
                    case 0x3f3787d2 {
                        /* setVerifierRouter() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let verifierRouter := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        if iszero(eq(caller(), sload(1))) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 38)
                            mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                            mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                            revert(0, 132)
                        }
                        let previousRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
                        {
                            let __ite_cond := eq(previousRouter, verifierRouter)
                            if __ite_cond {
                            }
                            if iszero(__ite_cond) {
                                if iszero(iszero(eq(verifierRouter, 0))) {
                                    {
                                        let __err_ptr := mload(64)
                                        mstore(add(__err_ptr, 0), 0x506f6f6c4164647265737349734e756c6c282900000000000000000000000000)
                                        let __err_hash := keccak256(__err_ptr, 19)
                                        let __err_selector := shl(224, shr(224, __err_hash))
                                        mstore(0, __err_selector)
                                        let __err_tail := 0
                                        revert(0, add(4, __err_tail))
                                    }
                                }
                                sstore(97642014805756523509931909943000448576722218578626833372473198353469753044997, and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
                                {
                                    let __evt_ptr := mload(64)
                                    mstore(add(__evt_ptr, 0), 0x5665726966696572526f757465725570646174656428616464726573732c6164)
                                    mstore(add(__evt_ptr, 32), 0x6472657373290000000000000000000000000000000000000000000000000000)
                                    let __evt_topic0 := keccak256(__evt_ptr, 38)
                                    log3(__evt_ptr, 0, __evt_topic0, and(previousRouter, 0xffffffffffffffffffffffffffffffffffffffff), and(verifierRouter, 0xffffffffffffffffffffffffffffffffffffffff))
                                }
                            }
                        }
                        stop()
                    }
                    case 0xf2fde38b {
                        /* transferOwnership() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let newOwner := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        if iszero(eq(caller(), sload(1))) {
                            mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                            mstore(4, 32)
                            mstore(36, 38)
                            mstore(68, 0x4163636573732064656e6965643a2063616c6c6572206973206e6f74206f776e)
                            mstore(100, 0x6572536c6f740000000000000000000000000000000000000000000000000000)
                            revert(0, 132)
                        }
                        sstore(2, and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
                        stop()
                    }
                    case 0x79ba5097 {
                        /* acceptOwnership() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        let sender := caller()
                        let pending := sload(2)
                        if iszero(eq(sender, pending)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x43616c6c65724e6f7450656e64696e674f776e65722829000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 23)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        sstore(1, and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
                        sstore(2, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
                        stop()
                    }
                    case 0xac75a6b3 {
                        /* countNonZero() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let values_offset := calldataload(4)
                        if lt(values_offset, 64) {
                            revert(0, 0)
                        }
                        let values_abs_offset := add(4, values_offset)
                        if gt(values_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let values_length := calldataload(values_abs_offset)
                        let values_tail_head_end := add(values_abs_offset, 32)
                        let values_tail_remaining := sub(calldatasize(), values_tail_head_end)
                        if gt(values_length, div(values_tail_remaining, 32)) {
                            revert(0, 0)
                        }
                        let values_data_offset := values_tail_head_end
                        let excludeIndex := calldataload(36)
                        let count := 0
                        for {
                            let j := 0
                        } lt(j, values_length) {
                            j := add(j, 1)
                        } {
                            if iszero(eq(j, excludeIndex)) {
                                let value := __verity_array_element_calldata_checked(values_data_offset, values_length, j)
                                if iszero(eq(value, 0)) {
                                    count := add(count, 1)
                                }
                            }
                        }
                        mstore(0, count)
                        return(0, 32)
                    }
                    case 0x23a9b5ea {
                        /* spendNullifiers() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let nullifierHashes_offset := calldataload(4)
                        if lt(nullifierHashes_offset, 32) {
                            revert(0, 0)
                        }
                        let nullifierHashes_abs_offset := add(4, nullifierHashes_offset)
                        if gt(nullifierHashes_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let nullifierHashes_length := calldataload(nullifierHashes_abs_offset)
                        let nullifierHashes_tail_head_end := add(nullifierHashes_abs_offset, 32)
                        let nullifierHashes_tail_remaining := sub(calldatasize(), nullifierHashes_tail_head_end)
                        if gt(nullifierHashes_length, div(nullifierHashes_tail_remaining, 32)) {
                            revert(0, 0)
                        }
                        let nullifierHashes_data_offset := nullifierHashes_tail_head_end
                        for {
                            let k := 0
                        } lt(k, nullifierHashes_length) {
                            k := add(k, 1)
                        } {
                            let nullifierHash := __verity_array_element_calldata_checked(nullifierHashes_data_offset, nullifierHashes_length, k)
                            if iszero(eq(nullifierHash, 0)) {
                                sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044996, nullifierHash), 1)
                            }
                        }
                        stop()
                    }
                    case 0x143ab017 {
                        /* realCommitments() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let newCommitments_offset := calldataload(4)
                        if lt(newCommitments_offset, 64) {
                            revert(0, 0)
                        }
                        let newCommitments_abs_offset := add(4, newCommitments_offset)
                        if gt(newCommitments_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let newCommitments_length := calldataload(newCommitments_abs_offset)
                        let newCommitments_tail_head_end := add(newCommitments_abs_offset, 32)
                        let newCommitments_tail_remaining := sub(calldatasize(), newCommitments_tail_head_end)
                        if gt(newCommitments_length, div(newCommitments_tail_remaining, 32)) {
                            revert(0, 0)
                        }
                        let newCommitments_data_offset := newCommitments_tail_head_end
                        let excludeIndex := calldataload(36)
                        let len := newCommitments_length
                        let count := 0
                        for {
                            let i := 0
                        } lt(i, len) {
                            i := add(i, 1)
                        } {
                            let commitment := __verity_array_element_calldata_checked(newCommitments_data_offset, newCommitments_length, i)
                            if iszero(eq(i, excludeIndex)) {
                                if iszero(eq(commitment, 0)) {
                                    count := add(count, 1)
                                }
                            }
                        }
                        let leaves_length := count
                        let leaves_data_offset := add(mload(64), 32)
                        mstore(sub(leaves_data_offset, 32), leaves_length)
                        mstore(64, add(leaves_data_offset, mul(leaves_length, 32)))
                        let j := 0
                        for {
                            let i := 0
                        } lt(i, len) {
                            i := add(i, 1)
                        } {
                            let commitment := __verity_array_element_calldata_checked(newCommitments_data_offset, newCommitments_length, i)
                            if iszero(eq(i, excludeIndex)) {
                                if iszero(eq(commitment, 0)) {
                                    mstore(add(leaves_data_offset, mul(j, 32)), commitment)
                                    j := add(j, 1)
                                }
                            }
                        }
                        mstore(0, 32)
                        mstore(32, leaves_length)
                        calldatacopy(64, leaves_data_offset, mul(leaves_length, 32))
                        return(0, add(64, mul(leaves_length, 32)))
                    }
                    case 0x406a7a7e {
                        /* realNullifiers() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let nullifierHashes_offset := calldataload(4)
                        if lt(nullifierHashes_offset, 32) {
                            revert(0, 0)
                        }
                        let nullifierHashes_abs_offset := add(4, nullifierHashes_offset)
                        if gt(nullifierHashes_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let nullifierHashes_length := calldataload(nullifierHashes_abs_offset)
                        let nullifierHashes_tail_head_end := add(nullifierHashes_abs_offset, 32)
                        let nullifierHashes_tail_remaining := sub(calldatasize(), nullifierHashes_tail_head_end)
                        if gt(nullifierHashes_length, div(nullifierHashes_tail_remaining, 32)) {
                            revert(0, 0)
                        }
                        let nullifierHashes_data_offset := nullifierHashes_tail_head_end
                        let len := nullifierHashes_length
                        let count := 0
                        for {
                            let i := 0
                        } lt(i, len) {
                            i := add(i, 1)
                        } {
                            let nullifierHash := __verity_array_element_calldata_checked(nullifierHashes_data_offset, nullifierHashes_length, i)
                            if iszero(eq(nullifierHash, 0)) {
                                count := add(count, 1)
                            }
                        }
                        let real_length := count
                        let real_data_offset := add(mload(64), 32)
                        mstore(sub(real_data_offset, 32), real_length)
                        mstore(64, add(real_data_offset, mul(real_length, 32)))
                        let j := 0
                        for {
                            let i := 0
                        } lt(i, len) {
                            i := add(i, 1)
                        } {
                            let nullifierHash := __verity_array_element_calldata_checked(nullifierHashes_data_offset, nullifierHashes_length, i)
                            if iszero(eq(nullifierHash, 0)) {
                                mstore(add(real_data_offset, mul(j, 32)), nullifierHash)
                                j := add(j, 1)
                            }
                        }
                        mstore(0, 32)
                        mstore(32, real_length)
                        calldatacopy(64, real_data_offset, mul(real_length, 32))
                        return(0, add(64, mul(real_length, 32)))
                    }
                    case 0x672d33ff {
                        /* lazyDefaultZero() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let index := calldataload(4)
                        let zero := 0
                        if eq(index, 1) {
                            zero := 14744269619966411208579211824598458697587494354926760081771325075741142829156
                        }
                        if eq(index, 2) {
                            zero := 7423237065226347324353380772367382631490014989348495481811164164159255474657
                        }
                        if eq(index, 3) {
                            zero := 11286972368698509976183087595462810875513684078608517520839298933882497716792
                        }
                        if eq(index, 4) {
                            zero := 3607627140608796879659380071776844901612302623152076817094415224584923813162
                        }
                        if eq(index, 5) {
                            zero := 19712377064642672829441595136074946683621277828620209496774504837737984048981
                        }
                        if eq(index, 6) {
                            zero := 20775607673010627194014556968476266066927294572720319469184847051418138353016
                        }
                        if eq(index, 7) {
                            zero := 3396914609616007258851405644437304192396347162513310381425243293
                        }
                        if eq(index, 8) {
                            zero := 21551820661461729022865262380882070649935529853313286572328683688269863701601
                        }
                        if eq(index, 9) {
                            zero := 6573136701248752079028194407151022595060682063033565181951145966236778420039
                        }
                        if eq(index, 10) {
                            zero := 12413880268183407374852357075976609371175688755676981206018884971008854919922
                        }
                        if eq(index, 11) {
                            zero := 14271763308400718165336499097156975241954733520325982997864342600795471836726
                        }
                        if eq(index, 12) {
                            zero := 20066985985293572387227381049700832219069292839614107140851619262827735677018
                        }
                        if eq(index, 13) {
                            zero := 9394776414966240069580838672673694685292165040808226440647796406499139370960
                        }
                        if eq(index, 14) {
                            zero := 11331146992410411304059858900317123658895005918277453009197229807340014528524
                        }
                        if eq(index, 15) {
                            zero := 15819538789928229930262697811477882737253464456578333862691129291651619515538
                        }
                        if eq(index, 16) {
                            zero := 19217088683336594659449020493828377907203207941212636669271704950158751593251
                        }
                        if eq(index, 17) {
                            zero := 21035245323335827719745544373081896983162834604456827698288649288827293579666
                        }
                        if eq(index, 18) {
                            zero := 6939770416153240137322503476966641397417391950902474480970945462551409848591
                        }
                        if eq(index, 19) {
                            zero := 10941962436777715901943463195175331263348098796018438960955633645115732864202
                        }
                        if eq(index, 20) {
                            zero := 15019797232609675441998260052101280400536945603062888308240081994073687793470
                        }
                        if eq(index, 21) {
                            zero := 11702828337982203149177882813338547876343922920234831094975924378932809409969
                        }
                        if eq(index, 22) {
                            zero := 11217067736778784455593535811108456786943573747466706329920902520905755780395
                        }
                        if eq(index, 23) {
                            zero := 16072238744996205792852194127671441602062027943016727953216607508365787157389
                        }
                        if eq(index, 24) {
                            zero := 17681057402012993898104192736393849603097507831571622013521167331642182653248
                        }
                        if eq(index, 25) {
                            zero := 21694045479371014653083846597424257852691458318143380497809004364947786214945
                        }
                        if eq(index, 26) {
                            zero := 8163447297445169709687354538480474434591144168767135863541048304198280615192
                        }
                        if eq(index, 27) {
                            zero := 14081762237856300239452543304351251708585712948734528663957353575674639038357
                        }
                        if eq(index, 28) {
                            zero := 16619959921569409661790279042024627172199214148318086837362003702249041851090
                        }
                        if eq(index, 29) {
                            zero := 7022159125197495734384997711896547675021391130223237843255817587255104160365
                        }
                        if eq(index, 30) {
                            zero := 4114686047564160449611603615418567457008101555090703535405891656262658644463
                        }
                        if eq(index, 31) {
                            zero := 12549363297364877722388257367377629555213421373705596078299904496781819142130
                        }
                        if eq(index, 32) {
                            zero := 21443572485391568159800782191812935835534334817699172242223315142338162256601
                        }
                        mstore(0, zero)
                        return(0, 32)
                    }
                    case 0x03283434 {
                        /* lazyIndexForElement() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let level := calldataload(4)
                        let index := calldataload(36)
                        mstore(0, add(mul(4294967295, level), index))
                        return(0, 32)
                    }
                    case 0x9a3d90f3 {
                        /* lazyInsert() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let leaf := calldataload(4)
                        let startIndex := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
                        let maxIndex := and(shr(0, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
                        if iszero(lt(leaf, 21888242871839275222246405745257275088548364400416034343698204186575808495617)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                                let __err_hash := keccak256(__err_ptr, 24)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(lt(startIndex, maxIndex)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                                let __err_hash := keccak256(__err_ptr, 24)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        {
                            let __compat_value := add(startIndex, 1)
                            let __compat_packed := and(__compat_value, 1099511627775)
                            let __compat_slot_word := sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)
                            let __compat_slot_cleared := and(__compat_slot_word, not(1208925819613529663078400))
                            sstore(97642014805756523509931909943000448576722218578626833372473198353469753044993, or(__compat_slot_cleared, shl(40, __compat_packed)))
                        }
                        let index := startIndex
                        let hash := leaf
                        let active := 1
                        for {
                            let level := 0
                        } lt(level, 32) {
                            level := add(level, 1)
                        } {
                            if iszero(eq(active, 0)) {
                                let elementKey := internal_internal_lazyIndexForElement(level, index)
                                sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, elementKey), hash)
                                {
                                    let __ite_cond := eq(and(index, 1), 0)
                                    if __ite_cond {
                                        active := 0
                                    }
                                    if iszero(__ite_cond) {
                                        let siblingKey := internal_internal_lazyIndexForElement(level, sub(index, 1))
                                        let sibling := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, siblingKey))
                                        let parent := internal_internal_poseidon2(sibling, hash)
                                        hash := parent
                                        index := shr(1, index)
                                    }
                                }
                            }
                        }
                        stop()
                    }
                    case 0xd63b96f5 {
                        /* lazyRootWithDepth32() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        let numberOfLeaves := and(shr(40, sload(97642014805756523509931909943000448576722218578626833372473198353469753044993)), 1099511627775)
                        {
                            let __ite_cond := eq(numberOfLeaves, 0)
                            if __ite_cond {
                                mstore(0, 21443572485391568159800782191812935835534334817699172242223315142338162256601)
                                return(0, 32)
                            }
                            if iszero(__ite_cond) {
                                let levels_length := 33
                                let levels_data_offset := add(mload(64), 32)
                                mstore(sub(levels_data_offset, 32), levels_length)
                                mstore(64, add(levels_data_offset, mul(levels_length, 32)))
                                let index := sub(numberOfLeaves, 1)
                                {
                                    let __ite_cond := eq(and(index, 1), 0)
                                    if __ite_cond {
                                        let elementKey := internal_internal_lazyIndexForElement(0, index)
                                        let element := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, elementKey))
                                        mstore(add(levels_data_offset, mul(0, 32)), element)
                                    }
                                    if iszero(__ite_cond) {
                                        mstore(add(levels_data_offset, mul(0, 32)), 0)
                                    }
                                }
                                for {
                                    let level := 0
                                } lt(level, 32) {
                                    level := add(level, 1)
                                } {
                                    let current := __verity_array_element_memory_checked(levels_data_offset, levels_length, level)
                                    {
                                        let __ite_cond := eq(and(index, 1), 0)
                                        if __ite_cond {
                                            let z := internal_internal_lazyDefaultZero(level)
                                            let parent := internal_internal_poseidon2(current, z)
                                            mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                                        }
                                        if iszero(__ite_cond) {
                                            let levelCount := shr(add(level, 1), numberOfLeaves)
                                            let parentIndex := shr(1, index)
                                            {
                                                let __ite_cond := gt(levelCount, parentIndex)
                                                if __ite_cond {
                                                    let parentKey := internal_internal_lazyIndexForElement(add(level, 1), parentIndex)
                                                    let parent := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, parentKey))
                                                    mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                                                }
                                                if iszero(__ite_cond) {
                                                    let siblingKey := internal_internal_lazyIndexForElement(level, sub(index, 1))
                                                    let sibling := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044994, siblingKey))
                                                    let parent := internal_internal_poseidon2(sibling, current)
                                                    mstore(add(levels_data_offset, mul(add(level, 1), 32)), parent)
                                                }
                                            }
                                        }
                                    }
                                    index := shr(1, index)
                                }
                                mstore(0, __verity_array_element_memory_checked(levels_data_offset, levels_length, 32))
                                return(0, 32)
                            }
                        }
                    }
                    case 0x176764b5 {
                        /* insertLeaves() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let leafHashes_offset := calldataload(4)
                        if lt(leafHashes_offset, 32) {
                            revert(0, 0)
                        }
                        let leafHashes_abs_offset := add(4, leafHashes_offset)
                        if gt(leafHashes_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let leafHashes_length := calldataload(leafHashes_abs_offset)
                        let leafHashes_tail_head_end := add(leafHashes_abs_offset, 32)
                        let leafHashes_tail_remaining := sub(calldatasize(), leafHashes_tail_head_end)
                        if gt(leafHashes_length, div(leafHashes_tail_remaining, 32)) {
                            revert(0, 0)
                        }
                        let leafHashes_data_offset := leafHashes_tail_head_end
                        let count := leafHashes_length
                        {
                            let __ite_cond := eq(count, 0)
                            if __ite_cond {
                                let currentRoot := sload(97642014805756523509931909943000448576722218578626833372473198353469753044992)
                                mstore(0, currentRoot)
                                return(0, 32)
                            }
                            if iszero(__ite_cond) {
                                for {
                                    let m := 0
                                } lt(m, count) {
                                    m := add(m, 1)
                                } {
                                    let leaf := __verity_array_element_calldata_checked(leafHashes_data_offset, leafHashes_length, m)
                                    internal_internal_lazyInsert(leaf)
                                }
                            }
                        }
                        let newRoot := internal_internal_lazyRootWithDepth32()
                        sstore(97642014805756523509931909943000448576722218578626833372473198353469753044992, newRoot)
                        sstore(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044995, newRoot), 1)
                        mstore(0, newRoot)
                        return(0, 32)
                    }
                    case 0xda2a81d6 {
                        /* computeContextHash() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let ciphertexts_offset := calldataload(4)
                        if lt(ciphertexts_offset, 32) {
                            revert(0, 0)
                        }
                        let ciphertexts_abs_offset := add(4, ciphertexts_offset)
                        if gt(ciphertexts_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let ciphertexts_length := calldataload(ciphertexts_abs_offset)
                        let ciphertexts_tail_head_end := add(ciphertexts_abs_offset, 32)
                        let ciphertexts_tail_remaining := sub(calldatasize(), ciphertexts_tail_head_end)
                        if gt(ciphertexts_length, div(ciphertexts_tail_remaining, 128)) {
                            revert(0, 0)
                        }
                        let ciphertexts_data_offset := ciphertexts_tail_head_end
                        let cid := chainid()
                        let selfAddr := address()
                        {
                            let __ciphertextsHash_abi_array_ptr := mload(64)
                            mstore(__ciphertextsHash_abi_array_ptr, 32)
                            mstore(add(__ciphertextsHash_abi_array_ptr, 32), ciphertexts_length)
                            let __ciphertextsHash_abi_array_data_bytes := mul(ciphertexts_length, 128)
                            calldatacopy(add(__ciphertextsHash_abi_array_ptr, 64), ciphertexts_data_offset, __ciphertextsHash_abi_array_data_bytes)
                            let __ciphertextsHash_abi_array_total_bytes := add(64, __ciphertextsHash_abi_array_data_bytes)
                            let __ciphertextsHash_abi_array_padded_total := and(add(__ciphertextsHash_abi_array_total_bytes, 31), not(31))
                            mstore(64, add(__ciphertextsHash_abi_array_ptr, __ciphertextsHash_abi_array_padded_total))
                            let ciphertextsHash := keccak256(__ciphertextsHash_abi_array_ptr, __ciphertextsHash_abi_array_total_bytes)
                        }
                        {
                            let __packed_word_0 := cid
                            let __packed_word_1 := selfAddr
                            let __packed_word_2 := ciphertextsHash
                            mstore(0, __packed_word_0)
                            mstore(32, __packed_word_1)
                            mstore(64, __packed_word_2)
                        }
                        let rawContext := keccak256(0, 96)
                        mstore(0, mod(rawContext, 21888242871839275222246405745257275088548364400416034343698204186575808495617))
                        return(0, 32)
                    }
                    case 0x1f51ab50 {
                        /* validateContext() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        let merkleRoot := calldataload(4)
                        let contextHash := calldataload(36)
                        let expectedContext := calldataload(68)
                        if iszero(eq(contextHash, expectedContext)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964436f6e746578744861736828290000000000000000)
                                let __err_hash := keccak256(__err_ptr, 24)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let rootSeen := sload(mappingSlot(97642014805756523509931909943000448576722218578626833372473198353469753044995, merkleRoot))
                        if iszero(iszero(eq(rootSeen, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644d65726b6c65526f6f742829000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 23)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        stop()
                    }
                    case 0x0f3c4bfc {
                        /* settleWithdrawalTransfer() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 100) {
                            revert(0, 0)
                        }
                        let token := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let recipient := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                        let amount := calldataload(68)
                        let selfAddr := address()
                        {
                            mstore(0, shl(224, 0x70a08231))
                            mstore(4, selfAddr)
                            let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                            if iszero(__balanceOf_success) {
                                let __balanceOf_rds := returndatasize()
                                returndatacopy(0, 0, __balanceOf_rds)
                                revert(0, __balanceOf_rds)
                            }
                            if iszero(eq(returndatasize(), 32)) {
                                revert(0, 0)
                            }
                        }
                        let poolBefore := mload(0)
                        {
                            mstore(0, shl(224, 0x70a08231))
                            mstore(4, recipient)
                            let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                            if iszero(__balanceOf_success) {
                                let __balanceOf_rds := returndatasize()
                                returndatacopy(0, 0, __balanceOf_rds)
                                revert(0, __balanceOf_rds)
                            }
                            if iszero(eq(returndatasize(), 32)) {
                                revert(0, 0)
                            }
                        }
                        let recipientBefore := mload(0)
                        {
                            mstore(0, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                            mstore(4, recipient)
                            mstore(36, amount)
                            let __st_success := call(gas(), token, 0, 0, 68, 0, 32)
                            if iszero(__st_success) {
                                mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                mstore(4, 32)
                                mstore(36, 17)
                                mstore(68, 0x7472616e73666572207265766572746564000000000000000000000000000000)
                                revert(0, 100)
                            }
                            if eq(returndatasize(), 32) {
                                if iszero(mload(0)) {
                                    mstore(0, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                                    mstore(4, 32)
                                    mstore(36, 23)
                                    mstore(68, 0x7472616e736665722072657475726e65642066616c7365000000000000000000)
                                    revert(0, 100)
                                }
                            }
                        }
                        {
                            mstore(0, shl(224, 0x70a08231))
                            mstore(4, selfAddr)
                            let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                            if iszero(__balanceOf_success) {
                                let __balanceOf_rds := returndatasize()
                                returndatacopy(0, 0, __balanceOf_rds)
                                revert(0, __balanceOf_rds)
                            }
                            if iszero(eq(returndatasize(), 32)) {
                                revert(0, 0)
                            }
                        }
                        let poolAfter := mload(0)
                        {
                            mstore(0, shl(224, 0x70a08231))
                            mstore(4, recipient)
                            let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                            if iszero(__balanceOf_success) {
                                let __balanceOf_rds := returndatasize()
                                returndatacopy(0, 0, __balanceOf_rds)
                                revert(0, __balanceOf_rds)
                            }
                            if iszero(eq(returndatasize(), 32)) {
                                revert(0, 0)
                            }
                        }
                        let recipientAfter := mload(0)
                        if iszero(eq(sub(poolBefore, poolAfter), amount)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c576974686472617742616c616e63654d69736d617463682829000000)
                                let __err_hash := keccak256(__err_ptr, 29)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(eq(sub(recipientAfter, recipientBefore), amount)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c576974686472617742616c616e63654d69736d617463682829000000)
                                let __err_hash := keccak256(__err_ptr, 29)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        stop()
                    }
                    case 0xa1662717 {
                        /* transferWithBalanceCheck() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 164) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 260) {
                            revert(0, 0)
                        }
                        let permit_0_0 := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let permit_0_1 := calldataload(36)
                        let permit_1 := calldataload(68)
                        let permit_2 := calldataload(100)
                        let depositor := and(calldataload(132), 0xffffffffffffffffffffffffffffffffffffffff)
                        let signature_offset := calldataload(164)
                        if lt(signature_offset, 256) {
                            revert(0, 0)
                        }
                        let signature_abs_offset := add(4, signature_offset)
                        if gt(signature_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let signature_length := calldataload(signature_abs_offset)
                        let signature_tail_head_end := add(signature_abs_offset, 32)
                        let signature_tail_remaining := sub(calldatasize(), signature_tail_head_end)
                        if gt(signature_length, signature_tail_remaining) {
                            revert(0, 0)
                        }
                        let signature_data_offset := signature_tail_head_end
                        let totalAmount := calldataload(196)
                        let witness := calldataload(228)
                        let selfAddr := address()
                        let token := permit_0_0
                        {
                            mstore(0, shl(224, 0x70a08231))
                            mstore(4, selfAddr)
                            let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                            if iszero(__balanceOf_success) {
                                let __balanceOf_rds := returndatasize()
                                returndatacopy(0, 0, __balanceOf_rds)
                                revert(0, __balanceOf_rds)
                            }
                            if iszero(eq(returndatasize(), 32)) {
                                revert(0, 0)
                            }
                        }
                        let balBefore := mload(0)
                        let permitCallOk, permitAccepted := permitWitnessTransferFrom_try(sload(98021192859356073326120044313192698615125063568118942569962362705841075886849), token, permit_0_1, permit_1, permit_2, selfAddr, totalAmount, depositor, witness, signature_data_offset, signature_length)
                        if iszero(permitCallOk) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                                let __err_hash := keccak256(__err_ptr, 28)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(permitAccepted) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                                let __err_hash := keccak256(__err_ptr, 28)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        {
                            mstore(0, shl(224, 0x70a08231))
                            mstore(4, selfAddr)
                            let __balanceOf_success := staticcall(gas(), token, 0, 36, 0, 32)
                            if iszero(__balanceOf_success) {
                                let __balanceOf_rds := returndatasize()
                                returndatacopy(0, 0, __balanceOf_rds)
                                revert(0, __balanceOf_rds)
                            }
                            if iszero(eq(returndatasize(), 32)) {
                                revert(0, 0)
                            }
                        }
                        let balAfter := mload(0)
                        if iszero(eq(sub(balAfter, balBefore), totalAmount)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c4465706f73697442616c616e63654d69736d61746368282900000000)
                                let __err_hash := keccak256(__err_ptr, 28)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        stop()
                    }
                    case 0x729ebff3 {
                        /* deposit() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 164) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 260) {
                            revert(0, 0)
                        }
                        let depositor := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let notes_offset := calldataload(36)
                        if lt(notes_offset, 256) {
                            revert(0, 0)
                        }
                        let notes_abs_offset := add(4, notes_offset)
                        if gt(notes_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let notes_length := calldataload(notes_abs_offset)
                        let notes_tail_head_end := add(notes_abs_offset, 32)
                        let notes_tail_remaining := sub(calldatasize(), notes_tail_head_end)
                        if gt(notes_length, div(notes_tail_remaining, 96)) {
                            revert(0, 0)
                        }
                        let notes_data_offset := notes_tail_head_end
                        let ciphertexts_offset := calldataload(68)
                        if lt(ciphertexts_offset, 256) {
                            revert(0, 0)
                        }
                        let ciphertexts_abs_offset := add(4, ciphertexts_offset)
                        if gt(ciphertexts_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let ciphertexts_length := calldataload(ciphertexts_abs_offset)
                        let ciphertexts_tail_head_end := add(ciphertexts_abs_offset, 32)
                        let ciphertexts_tail_remaining := sub(calldatasize(), ciphertexts_tail_head_end)
                        if gt(ciphertexts_length, div(ciphertexts_tail_remaining, 128)) {
                            revert(0, 0)
                        }
                        let ciphertexts_data_offset := ciphertexts_tail_head_end
                        let permit_0_0 := and(calldataload(100), 0xffffffffffffffffffffffffffffffffffffffff)
                        let permit_0_1 := calldataload(132)
                        let permit_1 := calldataload(164)
                        let permit_2 := calldataload(196)
                        let signature_offset := calldataload(228)
                        if lt(signature_offset, 256) {
                            revert(0, 0)
                        }
                        let signature_abs_offset := add(4, signature_offset)
                        if gt(signature_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let signature_length := calldataload(signature_abs_offset)
                        let signature_tail_head_end := add(signature_abs_offset, 32)
                        let signature_tail_remaining := sub(calldatasize(), signature_tail_head_end)
                        if gt(signature_length, signature_tail_remaining) {
                            revert(0, 0)
                        }
                        let signature_data_offset := signature_tail_head_end
                        internal___modifier_onlyRelayer()
                        let notesLen := notes_length
                        if iszero(iszero(eq(notesLen, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c456d7074794e6f746573282900000000000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 16)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(eq(ciphertexts_length, notesLen)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                                let __err_hash := keccak256(__err_ptr, 29)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let newLeaves_length := notesLen
                        let newLeaves_data_offset := add(mload(64), 32)
                        mstore(sub(newLeaves_data_offset, 32), newLeaves_length)
                        mstore(64, add(newLeaves_data_offset, mul(newLeaves_length, 32)))
                        for {
                            let noteIndex := 0
                        } lt(noteIndex, notesLen) {
                            noteIndex := add(noteIndex, 1)
                        } {
                            let npk := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 0)
                            let token := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 1)
                            let amount := __verity_array_element_word_calldata_checked(notes_data_offset, notes_length, noteIndex, 3, 2)
                            internal_internal_validateNoteFields(npk, token, amount)
                            if iszero(eq(token, permit_0_0)) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c546f6b656e4d69736d61746368282900000000000000000000000000)
                                    let __err_hash := keccak256(__err_ptr, 19)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            let leaf := internal_internal_hashNote(npk, token, amount)
                            mstore(add(newLeaves_data_offset, mul(noteIndex, 32)), leaf)
                        }
                        let totalAmount := internal_internal_sumNoteAmounts(notes_data_offset, notes_length)
                        let selfAddr := address()
                        {
                            let __notesHash_abi_two_arrays_ptr := mload(64)
                            let __notesHash_abi_array_a_data_bytes := mul(notesLen, 96)
                            let __notesHash_abi_array_b_data_bytes := mul(ciphertexts_length, 128)
                            let __notesHash_abi_array_a_tail_bytes := add(32, __notesHash_abi_array_a_data_bytes)
                            let __notesHash_abi_array_b_tail_bytes := add(32, __notesHash_abi_array_b_data_bytes)
                            let __notesHash_abi_array_b_head_offset := add(64, __notesHash_abi_array_a_tail_bytes)
                            let __notesHash_abi_two_arrays_total_bytes := add(__notesHash_abi_array_b_head_offset, __notesHash_abi_array_b_tail_bytes)
                            mstore(__notesHash_abi_two_arrays_ptr, 64)
                            mstore(add(__notesHash_abi_two_arrays_ptr, 32), __notesHash_abi_array_b_head_offset)
                            mstore(add(__notesHash_abi_two_arrays_ptr, 64), notesLen)
                            calldatacopy(add(__notesHash_abi_two_arrays_ptr, 96), notes_data_offset, __notesHash_abi_array_a_data_bytes)
                            mstore(add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_array_b_head_offset), ciphertexts_length)
                            calldatacopy(add(add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_array_b_head_offset), 32), ciphertexts_data_offset, __notesHash_abi_array_b_data_bytes)
                            let __notesHash_abi_two_arrays_padded_total := and(add(__notesHash_abi_two_arrays_total_bytes, 31), not(31))
                            mstore(64, add(__notesHash_abi_two_arrays_ptr, __notesHash_abi_two_arrays_padded_total))
                            let notesHash := keccak256(__notesHash_abi_two_arrays_ptr, __notesHash_abi_two_arrays_total_bytes)
                        }
                        {
                            let __packed_word_0 := 85194627925618981451180140414236292804855281853588093248984713240396722975024
                            let __packed_word_1 := selfAddr
                            let __packed_word_2 := notesHash
                            mstore(0, __packed_word_0)
                            mstore(32, __packed_word_1)
                            mstore(64, __packed_word_2)
                        }
                        let witness := keccak256(0, 96)
                        internal_internal_transferWithBalanceCheck(permit_0_0, permit_0_1, permit_1, permit_2, depositor, signature_data_offset, signature_length, totalAmount, witness)
                        let startIndex := internal_internal_nextLeafIndex()
                        let newRoot := internal_internal_insertLeaves(newLeaves_data_offset, newLeaves_length)
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x4465706f736974656428616464726573732c75696e743235362c75696e743235)
                            mstore(add(__evt_ptr, 32), 0x362c2875696e743235362c616464726573732c75696e74323536295b5d2c2875)
                            mstore(add(__evt_ptr, 64), 0x696e743235362c75696e743235365b335d295b5d290000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 85)
                            let __evt_data_tail := 128
                            mstore(add(__evt_ptr, 0), newRoot)
                            mstore(add(__evt_ptr, 32), startIndex)
                            mstore(add(__evt_ptr, 64), __evt_data_tail)
                            let __evt_arg2_len := notes_length
                            let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                            mstore(__evt_arg2_dst, __evt_arg2_len)
                            let __evt_arg2_byte_len := mul(__evt_arg2_len, 96)
                            for {
                                let __evt_arg2_i := 0
                            } lt(__evt_arg2_i, __evt_arg2_len) {
                                __evt_arg2_i := add(__evt_arg2_i, 1)
                            } {
                                let __evt_arg2_elem_base := add(add(4, notes_offset), mul(__evt_arg2_i, 96))
                                let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 96))
                                mstore(add(__evt_arg2_out_base, 0), calldataload(add(__evt_arg2_elem_base, 0)))
                                mstore(add(__evt_arg2_out_base, 32), and(calldataload(add(__evt_arg2_elem_base, 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                                mstore(add(__evt_arg2_out_base, 64), calldataload(add(__evt_arg2_elem_base, 64)))
                            }
                            let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                            mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                            __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                            mstore(add(__evt_ptr, 96), __evt_data_tail)
                            let __evt_arg3_len := ciphertexts_length
                            let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                            mstore(__evt_arg3_dst, __evt_arg3_len)
                            let __evt_arg3_byte_len := mul(__evt_arg3_len, 128)
                            for {
                                let __evt_arg3_i := 0
                            } lt(__evt_arg3_i, __evt_arg3_len) {
                                __evt_arg3_i := add(__evt_arg3_i, 1)
                            } {
                                let __evt_arg3_elem_base := add(add(4, ciphertexts_offset), mul(__evt_arg3_i, 128))
                                let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 128))
                                mstore(add(__evt_arg3_out_base, 0), calldataload(add(__evt_arg3_elem_base, 0)))
                                mstore(add(__evt_arg3_out_base, 32), calldataload(add(__evt_arg3_elem_base, 32)))
                                mstore(add(__evt_arg3_out_base, 64), calldataload(add(__evt_arg3_elem_base, 64)))
                                mstore(add(__evt_arg3_out_base, 96), calldataload(add(__evt_arg3_elem_base, 96)))
                            }
                            let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                            mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                            __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                            log2(__evt_ptr, __evt_data_tail, __evt_topic0, and(depositor, 0xffffffffffffffffffffffffffffffffffffffff))
                        }
                        stop()
                    }
                    case 0xb8987a57 {
                        /* transfer() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let transactions_offset := calldataload(4)
                        if lt(transactions_offset, 32) {
                            revert(0, 0)
                        }
                        let transactions_abs_offset := add(4, transactions_offset)
                        if gt(transactions_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let transactions_length := calldataload(transactions_abs_offset)
                        let transactions_tail_head_end := add(transactions_abs_offset, 32)
                        let transactions_tail_remaining := sub(calldatasize(), transactions_tail_head_end)
                        if gt(transactions_length, div(transactions_tail_remaining, 32)) {
                            revert(0, 0)
                        }
                        let transactions_data_offset := transactions_tail_head_end
                        internal___modifier_onlyRelayer()
                        let txLen := transactions_length
                        if iszero(iszero(eq(txLen, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 23)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        for {
                            let i := 0
                        } lt(i, txLen) {
                            i := add(i, 1)
                        } {
                            let verifierRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
                            let success, circuit_verifier, circuit_inputCount, circuit_outputCount, circuit_active := getCircuit_try(verifierRouter, __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 8))
                            if iszero(success) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                                    let __err_hash := keccak256(__err_ptr, 26)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            if iszero(iszero(eq(circuit_verifier, 0))) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                                    let __err_hash := keccak256(__err_ptr, 26)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            if iszero(iszero(eq(circuit_active, 0))) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c43697263756974496e61637469766528290000000000000000000000)
                                    let __err_hash := keccak256(__err_ptr, 21)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10), circuit_inputCount)) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964496e70757453686170652829000000000000000000)
                                    let __err_hash := keccak256(__err_ptr, 23)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11), circuit_outputCount)) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                                    let __err_hash := keccak256(__err_ptr, 24)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            let ciphertextCount := internal_internal_countNonZero(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 11), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11), 115792089237316195423570985008687907853269984665640564039457584007913129639935)
                            if iszero(eq(__verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13), ciphertextCount)) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                                    let __err_hash := keccak256(__err_ptr, 29)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            let computedContext := internal_internal_computeContextHash(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 13), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13))
                            internal_internal_validateContext(__verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 9), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 12), computedContext)
                            let proofOk, ok := verifySpend_try(circuit_verifier, __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 0), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 1), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 2), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 3), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 4), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 5), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 6), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 7), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 9), __verity_array_element_dynamic_word_calldata_checked(transactions_data_offset, transactions_length, i, 12), __verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 11), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11))
                            if iszero(proofOk) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                                    let __err_hash := keccak256(__err_ptr, 29)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            if iszero(ok) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                                    let __err_hash := keccak256(__err_ptr, 29)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            internal_internal_spendNullifiers(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 10), __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10))
                            let leavesCount := 0
                            for {
                                let commitCountIndex := 0
                            } lt(commitCountIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11)) {
                                commitCountIndex := add(commitCountIndex, 1)
                            } {
                                let commitment := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 11, commitCountIndex)
                                if iszero(eq(commitment, 0)) {
                                    leavesCount := add(leavesCount, 1)
                                }
                            }
                            let leaves_length := leavesCount
                            let leaves_data_offset := add(mload(64), 32)
                            mstore(sub(leaves_data_offset, 32), leaves_length)
                            mstore(64, add(leaves_data_offset, mul(leaves_length, 32)))
                            let leafWriteIndex := 0
                            for {
                                let commitWriteIndex := 0
                            } lt(commitWriteIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 11)) {
                                commitWriteIndex := add(commitWriteIndex, 1)
                            } {
                                let commitment := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 11, commitWriteIndex)
                                if iszero(eq(commitment, 0)) {
                                    mstore(add(leaves_data_offset, mul(leafWriteIndex, 32)), commitment)
                                    leafWriteIndex := add(leafWriteIndex, 1)
                                }
                            }
                            let nullifierCount := 0
                            for {
                                let nullifierCountIndex := 0
                            } lt(nullifierCountIndex, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10)) {
                                nullifierCountIndex := add(nullifierCountIndex, 1)
                            } {
                                let nullifierHash := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 10, nullifierCountIndex)
                                if iszero(eq(nullifierHash, 0)) {
                                    nullifierCount := add(nullifierCount, 1)
                                }
                            }
                            let realNulls_length := nullifierCount
                            let realNulls_data_offset := add(mload(64), 32)
                            mstore(sub(realNulls_data_offset, 32), realNulls_length)
                            mstore(64, add(realNulls_data_offset, mul(realNulls_length, 32)))
                            let nullifierWriteIndex := 0
                            for {
                                let nullifierWriteIndexLoop := 0
                            } lt(nullifierWriteIndexLoop, __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 10)) {
                                nullifierWriteIndexLoop := add(nullifierWriteIndexLoop, 1)
                            } {
                                let nullifierHash := __verity_array_element_dynamic_member_element_calldata_checked(transactions_data_offset, transactions_length, i, 10, nullifierWriteIndexLoop)
                                if iszero(eq(nullifierHash, 0)) {
                                    mstore(add(realNulls_data_offset, mul(nullifierWriteIndex, 32)), nullifierHash)
                                    nullifierWriteIndex := add(nullifierWriteIndex, 1)
                                }
                            }
                            let startIndex := internal_internal_nextLeafIndex()
                            let newRoot := internal_internal_insertLeaves(leaves_data_offset, leaves_length)
                            {
                                let __evt_ptr := mload(64)
                                mstore(add(__evt_ptr, 0), 0x5472616e736665727265642875696e743235362c75696e743235362c75696e74)
                                mstore(add(__evt_ptr, 32), 0x3235365b5d2c75696e743235365b5d2c2875696e743235362c75696e74323536)
                                mstore(add(__evt_ptr, 64), 0x5b335d295b5d2900000000000000000000000000000000000000000000000000)
                                let __evt_topic0 := keccak256(__evt_ptr, 71)
                                let __evt_data_tail := 128
                                mstore(add(__evt_ptr, 0), startIndex)
                                mstore(add(__evt_ptr, 32), __evt_data_tail)
                                let __evt_arg1_len := leaves_length
                                let __evt_arg1_dst := add(__evt_ptr, __evt_data_tail)
                                mstore(__evt_arg1_dst, __evt_arg1_len)
                                let __evt_arg1_byte_len := mul(__evt_arg1_len, 32)
                                for {
                                    let __evt_arg1_i := 0
                                } lt(__evt_arg1_i, __evt_arg1_len) {
                                    __evt_arg1_i := add(__evt_arg1_i, 1)
                                } {
                                    let __evt_arg1_elem_base := add(leaves_data_offset, mul(__evt_arg1_i, 32))
                                    let __evt_arg1_out_base := add(add(__evt_arg1_dst, 32), mul(__evt_arg1_i, 32))
                                    mstore(add(__evt_arg1_out_base, 0), mload(add(__evt_arg1_elem_base, 0)))
                                }
                                let __evt_arg1_padded := and(add(__evt_arg1_byte_len, 31), not(31))
                                mstore(add(add(__evt_arg1_dst, 32), __evt_arg1_byte_len), 0)
                                __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg1_padded))
                                mstore(add(__evt_ptr, 64), __evt_data_tail)
                                let __evt_arg2_len := realNulls_length
                                let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                                mstore(__evt_arg2_dst, __evt_arg2_len)
                                let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                                for {
                                    let __evt_arg2_i := 0
                                } lt(__evt_arg2_i, __evt_arg2_len) {
                                    __evt_arg2_i := add(__evt_arg2_i, 1)
                                } {
                                    let __evt_arg2_elem_base := add(realNulls_data_offset, mul(__evt_arg2_i, 32))
                                    let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                                    mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                                }
                                let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                                mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                                __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                                mstore(add(__evt_ptr, 96), __evt_data_tail)
                                let __evt_arg3_len := __verity_array_element_dynamic_member_length_calldata_checked(transactions_data_offset, transactions_length, i, 13)
                                let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                                mstore(__evt_arg3_dst, __evt_arg3_len)
                                let __evt_arg3_byte_len := mul(__evt_arg3_len, 128)
                                for {
                                    let __evt_arg3_i := 0
                                } lt(__evt_arg3_i, __evt_arg3_len) {
                                    __evt_arg3_i := add(__evt_arg3_i, 1)
                                } {
                                    let __evt_arg3_elem_base := add(__verity_array_element_dynamic_member_data_offset_calldata_checked(transactions_data_offset, transactions_length, i, 13), mul(__evt_arg3_i, 128))
                                    let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 128))
                                    mstore(add(__evt_arg3_out_base, 0), calldataload(add(__evt_arg3_elem_base, 0)))
                                    mstore(add(__evt_arg3_out_base, 32), calldataload(add(__evt_arg3_elem_base, 32)))
                                    mstore(add(__evt_arg3_out_base, 64), calldataload(add(__evt_arg3_elem_base, 64)))
                                    mstore(add(__evt_arg3_out_base, 96), calldataload(add(__evt_arg3_elem_base, 96)))
                                }
                                let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                                mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                                __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                                log2(__evt_ptr, __evt_data_tail, __evt_topic0, newRoot)
                            }
                        }
                        stop()
                    }
                    case 0x8f0b1b76 {
                        /* executeWithdrawal() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 68) {
                            revert(0, 0)
                        }
                        let txn_offset := calldataload(4)
                        if lt(txn_offset, 64) {
                            revert(0, 0)
                        }
                        let txn_abs_offset := add(4, txn_offset)
                        if gt(txn_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let txn_data_offset := txn_abs_offset
                        let emergency := iszero(iszero(calldataload(36)))
                        if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15), 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465416d6f756e742829000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 23)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f74654e504b2829000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 20)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(iszero(eq(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644e6f7465546f6b656e282900000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 22)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if gt(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), 1461501637330902918203684832716283019655932542975) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c526563697069656e742829)
                                let __err_hash := keccak256(__err_ptr, 32)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let recipient := __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13)
                        let selfAddr := address()
                        if iszero(iszero(eq(recipient, selfAddr))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c526563697069656e742829)
                                let __err_hash := keccak256(__err_ptr, 32)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let verifierRouter := sload(97642014805756523509931909943000448576722218578626833372473198353469753044997)
                        let success, circuit_verifier, circuit_inputCount, circuit_outputCount, circuit_active := getCircuit_try(verifierRouter, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 8))
                        if iszero(success) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                                let __err_hash := keccak256(__err_ptr, 26)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(iszero(eq(circuit_verifier, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c436972637569744e6f74526567697374657265642829000000000000)
                                let __err_hash := keccak256(__err_ptr, 26)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(iszero(eq(circuit_active, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c43697263756974496e61637469766528290000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 21)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10), circuit_inputCount)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c6964496e70757453686170652829000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 23)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11), circuit_outputCount)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69644f7574707574536861706528290000000000000000)
                                let __err_hash := keccak256(__err_ptr, 24)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let wSlot := sub(circuit_outputCount, 1)
                        let withdrawalCommitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, wSlot)
                        if iszero(iszero(eq(withdrawalCommitment, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c5769746864726177616c536c6f745a65726f28290000000000000000)
                                let __err_hash := keccak256(__err_ptr, 24)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let noteHash := internal_internal_hashNote(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 13), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15))
                        if iszero(eq(withdrawalCommitment, noteHash)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c496e76616c69645769746864726177616c436f6d6d69746d656e7428)
                                mstore(add(__err_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 33)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let ciphertextCount := internal_internal_countNonZero(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 11), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11), wSlot)
                        if iszero(eq(__verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16), ciphertextCount)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c43697068657274657874436f756e744d69736d617463682829000000)
                                let __err_hash := keccak256(__err_ptr, 29)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let computedContext := internal_internal_computeContextHash(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16))
                        internal_internal_validateContext(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 9), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 12), computedContext)
                        let proofOk, ok := verifySpend_try(circuit_verifier, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 0), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 1), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 2), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 3), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 4), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 5), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 6), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 7), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 9), __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 12), __verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 11), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11))
                        if iszero(proofOk) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                                let __err_hash := keccak256(__err_ptr, 29)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(ok) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c50726f6f66566572696669636174696f6e4661696c65642829000000)
                                let __err_hash := keccak256(__err_ptr, 29)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        internal_internal_spendNullifiers(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 10), __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10))
                        let leavesCount := 0
                        for {
                            let withdrawCommitCountIndex := 0
                        } lt(withdrawCommitCountIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11)) {
                            withdrawCommitCountIndex := add(withdrawCommitCountIndex, 1)
                        } {
                            let commitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, withdrawCommitCountIndex)
                            if iszero(eq(withdrawCommitCountIndex, wSlot)) {
                                if iszero(eq(commitment, 0)) {
                                    leavesCount := add(leavesCount, 1)
                                }
                            }
                        }
                        let leaves_length := leavesCount
                        let leaves_data_offset := add(mload(64), 32)
                        mstore(sub(leaves_data_offset, 32), leaves_length)
                        mstore(64, add(leaves_data_offset, mul(leaves_length, 32)))
                        let leafWriteIndex := 0
                        for {
                            let withdrawCommitWriteIndex := 0
                        } lt(withdrawCommitWriteIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 11)) {
                            withdrawCommitWriteIndex := add(withdrawCommitWriteIndex, 1)
                        } {
                            let commitment := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 11, withdrawCommitWriteIndex)
                            if iszero(eq(withdrawCommitWriteIndex, wSlot)) {
                                if iszero(eq(commitment, 0)) {
                                    mstore(add(leaves_data_offset, mul(leafWriteIndex, 32)), commitment)
                                    leafWriteIndex := add(leafWriteIndex, 1)
                                }
                            }
                        }
                        let nullifierCount := 0
                        for {
                            let withdrawNullifierCountIndex := 0
                        } lt(withdrawNullifierCountIndex, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10)) {
                            withdrawNullifierCountIndex := add(withdrawNullifierCountIndex, 1)
                        } {
                            let nullifierHash := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 10, withdrawNullifierCountIndex)
                            if iszero(eq(nullifierHash, 0)) {
                                nullifierCount := add(nullifierCount, 1)
                            }
                        }
                        let realNulls_length := nullifierCount
                        let realNulls_data_offset := add(mload(64), 32)
                        mstore(sub(realNulls_data_offset, 32), realNulls_length)
                        mstore(64, add(realNulls_data_offset, mul(realNulls_length, 32)))
                        let nullifierWriteIndex := 0
                        for {
                            let withdrawNullifierWriteIndexLoop := 0
                        } lt(withdrawNullifierWriteIndexLoop, __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 10)) {
                            withdrawNullifierWriteIndexLoop := add(withdrawNullifierWriteIndexLoop, 1)
                        } {
                            let nullifierHash := __verity_param_dynamic_member_element_calldata_checked(txn_data_offset, 10, withdrawNullifierWriteIndexLoop)
                            if iszero(eq(nullifierHash, 0)) {
                                mstore(add(realNulls_data_offset, mul(nullifierWriteIndex, 32)), nullifierHash)
                                nullifierWriteIndex := add(nullifierWriteIndex, 1)
                            }
                        }
                        let startIndex := internal_internal_nextLeafIndex()
                        let newRoot := internal_internal_insertLeaves(leaves_data_offset, leaves_length)
                        internal_internal_settleWithdrawalTransfer(__verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 14), recipient, __verity_param_dynamic_head_word_calldata_checked(txn_data_offset, 15))
                        {
                            let __ite_cond := emergency
                            if __ite_cond {
                                {
                                    let __evt_ptr := mload(64)
                                    mstore(add(__evt_ptr, 0), 0x456d657267656e637957697468647261776e28616464726573732c2875696e74)
                                    mstore(add(__evt_ptr, 32), 0x3235362c616464726573732c75696e74323536292c75696e743235362c75696e)
                                    mstore(add(__evt_ptr, 64), 0x743235362c75696e743235365b5d2c75696e743235365b5d2c2875696e743235)
                                    mstore(add(__evt_ptr, 96), 0x362c75696e743235365b335d295b5d2900000000000000000000000000000000)
                                    let __evt_topic0 := keccak256(__evt_ptr, 112)
                                    let __evt_data_tail := 224
                                    mstore(add(add(__evt_ptr, 0), 0), calldataload(add(add(txn_data_offset, 416), 0)))
                                    mstore(add(add(__evt_ptr, 0), 32), and(calldataload(add(add(txn_data_offset, 416), 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                                    mstore(add(add(__evt_ptr, 0), 64), calldataload(add(add(txn_data_offset, 416), 64)))
                                    mstore(add(__evt_ptr, 96), startIndex)
                                    mstore(add(__evt_ptr, 128), __evt_data_tail)
                                    let __evt_arg2_len := leaves_length
                                    let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                                    mstore(__evt_arg2_dst, __evt_arg2_len)
                                    let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                                    for {
                                        let __evt_arg2_i := 0
                                    } lt(__evt_arg2_i, __evt_arg2_len) {
                                        __evt_arg2_i := add(__evt_arg2_i, 1)
                                    } {
                                        let __evt_arg2_elem_base := add(leaves_data_offset, mul(__evt_arg2_i, 32))
                                        let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                                        mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                                    }
                                    let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                                    mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                                    mstore(add(__evt_ptr, 160), __evt_data_tail)
                                    let __evt_arg3_len := realNulls_length
                                    let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                                    mstore(__evt_arg3_dst, __evt_arg3_len)
                                    let __evt_arg3_byte_len := mul(__evt_arg3_len, 32)
                                    for {
                                        let __evt_arg3_i := 0
                                    } lt(__evt_arg3_i, __evt_arg3_len) {
                                        __evt_arg3_i := add(__evt_arg3_i, 1)
                                    } {
                                        let __evt_arg3_elem_base := add(realNulls_data_offset, mul(__evt_arg3_i, 32))
                                        let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 32))
                                        mstore(add(__evt_arg3_out_base, 0), mload(add(__evt_arg3_elem_base, 0)))
                                    }
                                    let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                                    mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                                    mstore(add(__evt_ptr, 192), __evt_data_tail)
                                    let __evt_arg4_len := __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16)
                                    let __evt_arg4_dst := add(__evt_ptr, __evt_data_tail)
                                    mstore(__evt_arg4_dst, __evt_arg4_len)
                                    let __evt_arg4_byte_len := mul(__evt_arg4_len, 128)
                                    for {
                                        let __evt_arg4_i := 0
                                    } lt(__evt_arg4_i, __evt_arg4_len) {
                                        __evt_arg4_i := add(__evt_arg4_i, 1)
                                    } {
                                        let __evt_arg4_elem_base := add(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), mul(__evt_arg4_i, 128))
                                        let __evt_arg4_out_base := add(add(__evt_arg4_dst, 32), mul(__evt_arg4_i, 128))
                                        mstore(add(__evt_arg4_out_base, 0), calldataload(add(__evt_arg4_elem_base, 0)))
                                        mstore(add(__evt_arg4_out_base, 32), calldataload(add(__evt_arg4_elem_base, 32)))
                                        mstore(add(__evt_arg4_out_base, 64), calldataload(add(__evt_arg4_elem_base, 64)))
                                        mstore(add(__evt_arg4_out_base, 96), calldataload(add(__evt_arg4_elem_base, 96)))
                                    }
                                    let __evt_arg4_padded := and(add(__evt_arg4_byte_len, 31), not(31))
                                    mstore(add(add(__evt_arg4_dst, 32), __evt_arg4_byte_len), 0)
                                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg4_padded))
                                    log3(__evt_ptr, __evt_data_tail, __evt_topic0, and(recipient, 0xffffffffffffffffffffffffffffffffffffffff), newRoot)
                                }
                            }
                            if iszero(__ite_cond) {
                                {
                                    let __evt_ptr := mload(64)
                                    mstore(add(__evt_ptr, 0), 0x57697468647261776e28616464726573732c2875696e743235362c6164647265)
                                    mstore(add(__evt_ptr, 32), 0x73732c75696e74323536292c75696e743235362c75696e743235362c75696e74)
                                    mstore(add(__evt_ptr, 64), 0x3235365b5d2c75696e743235365b5d2c2875696e743235362c75696e74323536)
                                    mstore(add(__evt_ptr, 96), 0x5b335d295b5d2900000000000000000000000000000000000000000000000000)
                                    let __evt_topic0 := keccak256(__evt_ptr, 103)
                                    let __evt_data_tail := 224
                                    mstore(add(add(__evt_ptr, 0), 0), calldataload(add(add(txn_data_offset, 416), 0)))
                                    mstore(add(add(__evt_ptr, 0), 32), and(calldataload(add(add(txn_data_offset, 416), 32)), 0xffffffffffffffffffffffffffffffffffffffff))
                                    mstore(add(add(__evt_ptr, 0), 64), calldataload(add(add(txn_data_offset, 416), 64)))
                                    mstore(add(__evt_ptr, 96), startIndex)
                                    mstore(add(__evt_ptr, 128), __evt_data_tail)
                                    let __evt_arg2_len := leaves_length
                                    let __evt_arg2_dst := add(__evt_ptr, __evt_data_tail)
                                    mstore(__evt_arg2_dst, __evt_arg2_len)
                                    let __evt_arg2_byte_len := mul(__evt_arg2_len, 32)
                                    for {
                                        let __evt_arg2_i := 0
                                    } lt(__evt_arg2_i, __evt_arg2_len) {
                                        __evt_arg2_i := add(__evt_arg2_i, 1)
                                    } {
                                        let __evt_arg2_elem_base := add(leaves_data_offset, mul(__evt_arg2_i, 32))
                                        let __evt_arg2_out_base := add(add(__evt_arg2_dst, 32), mul(__evt_arg2_i, 32))
                                        mstore(add(__evt_arg2_out_base, 0), mload(add(__evt_arg2_elem_base, 0)))
                                    }
                                    let __evt_arg2_padded := and(add(__evt_arg2_byte_len, 31), not(31))
                                    mstore(add(add(__evt_arg2_dst, 32), __evt_arg2_byte_len), 0)
                                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg2_padded))
                                    mstore(add(__evt_ptr, 160), __evt_data_tail)
                                    let __evt_arg3_len := realNulls_length
                                    let __evt_arg3_dst := add(__evt_ptr, __evt_data_tail)
                                    mstore(__evt_arg3_dst, __evt_arg3_len)
                                    let __evt_arg3_byte_len := mul(__evt_arg3_len, 32)
                                    for {
                                        let __evt_arg3_i := 0
                                    } lt(__evt_arg3_i, __evt_arg3_len) {
                                        __evt_arg3_i := add(__evt_arg3_i, 1)
                                    } {
                                        let __evt_arg3_elem_base := add(realNulls_data_offset, mul(__evt_arg3_i, 32))
                                        let __evt_arg3_out_base := add(add(__evt_arg3_dst, 32), mul(__evt_arg3_i, 32))
                                        mstore(add(__evt_arg3_out_base, 0), mload(add(__evt_arg3_elem_base, 0)))
                                    }
                                    let __evt_arg3_padded := and(add(__evt_arg3_byte_len, 31), not(31))
                                    mstore(add(add(__evt_arg3_dst, 32), __evt_arg3_byte_len), 0)
                                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg3_padded))
                                    mstore(add(__evt_ptr, 192), __evt_data_tail)
                                    let __evt_arg4_len := __verity_param_dynamic_member_length_calldata_checked(txn_data_offset, 16)
                                    let __evt_arg4_dst := add(__evt_ptr, __evt_data_tail)
                                    mstore(__evt_arg4_dst, __evt_arg4_len)
                                    let __evt_arg4_byte_len := mul(__evt_arg4_len, 128)
                                    for {
                                        let __evt_arg4_i := 0
                                    } lt(__evt_arg4_i, __evt_arg4_len) {
                                        __evt_arg4_i := add(__evt_arg4_i, 1)
                                    } {
                                        let __evt_arg4_elem_base := add(__verity_param_dynamic_member_data_offset_calldata_checked(txn_data_offset, 16), mul(__evt_arg4_i, 128))
                                        let __evt_arg4_out_base := add(add(__evt_arg4_dst, 32), mul(__evt_arg4_i, 128))
                                        mstore(add(__evt_arg4_out_base, 0), calldataload(add(__evt_arg4_elem_base, 0)))
                                        mstore(add(__evt_arg4_out_base, 32), calldataload(add(__evt_arg4_elem_base, 32)))
                                        mstore(add(__evt_arg4_out_base, 64), calldataload(add(__evt_arg4_elem_base, 64)))
                                        mstore(add(__evt_arg4_out_base, 96), calldataload(add(__evt_arg4_elem_base, 96)))
                                    }
                                    let __evt_arg4_padded := and(add(__evt_arg4_byte_len, 31), not(31))
                                    mstore(add(add(__evt_arg4_dst, 32), __evt_arg4_byte_len), 0)
                                    __evt_data_tail := add(__evt_data_tail, add(32, __evt_arg4_padded))
                                    log3(__evt_ptr, __evt_data_tail, __evt_topic0, and(recipient, 0xffffffffffffffffffffffffffffffffffffffff), newRoot)
                                }
                            }
                        }
                        stop()
                    }
                    case 0x91cf6a2a {
                        /* withdraw() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let transactions_offset := calldataload(4)
                        if lt(transactions_offset, 32) {
                            revert(0, 0)
                        }
                        let transactions_abs_offset := add(4, transactions_offset)
                        if gt(transactions_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let transactions_length := calldataload(transactions_abs_offset)
                        let transactions_tail_head_end := add(transactions_abs_offset, 32)
                        let transactions_tail_remaining := sub(calldatasize(), transactions_tail_head_end)
                        if gt(transactions_length, div(transactions_tail_remaining, 32)) {
                            revert(0, 0)
                        }
                        let transactions_data_offset := transactions_tail_head_end
                        internal___modifier_onlyRelayer()
                        let txLen := transactions_length
                        if iszero(iszero(eq(txLen, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 23)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        for {
                            let i := 0
                        } lt(i, txLen) {
                            i := add(i, 1)
                        } {
                            internal_internal_executeWithdrawal(__verity_array_element_dynamic_data_offset_calldata_checked(transactions_data_offset, transactions_length, i), 0)
                        }
                        stop()
                    }
                    case 0xd51ae75a {
                        /* emergencyWithdraw() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let transactions_offset := calldataload(4)
                        if lt(transactions_offset, 32) {
                            revert(0, 0)
                        }
                        let transactions_abs_offset := add(4, transactions_offset)
                        if gt(transactions_abs_offset, sub(calldatasize(), 32)) {
                            revert(0, 0)
                        }
                        let transactions_length := calldataload(transactions_abs_offset)
                        let transactions_tail_head_end := add(transactions_abs_offset, 32)
                        let transactions_tail_remaining := sub(calldatasize(), transactions_tail_head_end)
                        if gt(transactions_length, div(transactions_tail_remaining, 32)) {
                            revert(0, 0)
                        }
                        let transactions_data_offset := transactions_tail_head_end
                        let txLen := transactions_length
                        if iszero(iszero(eq(txLen, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x506f6f6c456d7074795472616e73616374696f6e732829000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 23)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        for {
                            let i := 0
                        } lt(i, txLen) {
                            i := add(i, 1)
                        } {
                            internal_internal_executeWithdrawal(__verity_array_element_dynamic_data_offset_calldata_checked(transactions_data_offset, transactions_length, i), 1)
                        }
                        stop()
                    }
                    default {
                        revert(0, 0)
                    }
                }
            }
        }
    }
}