object "VerifierRouter" {
    code {
        if callvalue() {
            revert(0, 0)
        }
        function mappingSlot(baseSlot, key) -> slot {
            mstore(0, key)
            mstore(32, baseSlot)
            slot := keccak256(0, 64)
        }
        function internal_internal_owner() -> __ret0 {
            let current := sload(0)
            __ret0 := current
            leave
        }
        function internal_internal_pendingOwner() -> __ret0 {
            let pending := sload(1)
            __ret0 := pending
            leave
        }
        function internal_internal_transferOwnership(newOwner) {
            let sender := caller()
            let currentOwner := sload(0)
            if iszero(eq(sender, currentOwner)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                    mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 35)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 32
                    mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                    revert(0, add(4, __err_tail))
                }
            }
            sstore(1, and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
            {
                let __evt_ptr := mload(64)
                mstore(add(__evt_ptr, 0), 0x4f776e6572736869705472616e73666572537461727465642861646472657373)
                mstore(add(__evt_ptr, 32), 0x2c61646472657373290000000000000000000000000000000000000000000000)
                let __evt_topic0 := keccak256(__evt_ptr, 41)
                log3(__evt_ptr, 0, __evt_topic0, and(currentOwner, 0xffffffffffffffffffffffffffffffffffffffff), and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
            }
            stop()
        }
        function internal_internal_acceptOwnership() {
            let sender := caller()
            let pending := sload(1)
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
            let previousOwner := sload(0)
            sstore(0, and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
            sstore(1, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
            {
                let __evt_ptr := mload(64)
                mstore(add(__evt_ptr, 0), 0x4f776e6572736869705472616e7366657272656428616464726573732c616464)
                mstore(add(__evt_ptr, 32), 0x7265737329000000000000000000000000000000000000000000000000000000)
                let __evt_topic0 := keccak256(__evt_ptr, 37)
                log3(__evt_ptr, 0, __evt_topic0, and(previousOwner, 0xffffffffffffffffffffffffffffffffffffffff), and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
            }
            stop()
        }
        function internal_internal_setCircuit(circuitId, verifierAddr, inputCount, outputCount) {
            let sender := caller()
            let currentOwner := sload(0)
            if iszero(eq(sender, currentOwner)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                    mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 35)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 32
                    mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(iszero(eq(circuitId, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69644369726375697449642829)
                    let __err_hash := keccak256(__err_ptr, 32)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(iszero(eq(verifierAddr, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645665726966696572282900)
                    let __err_hash := keccak256(__err_ptr, 31)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let codeLen := extcodesize(verifierAddr)
            if iszero(iszero(eq(codeLen, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645665726966696572282900)
                    let __err_hash := keccak256(__err_ptr, 31)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(iszero(eq(inputCount, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645368617065282900000000)
                    let __err_hash := keccak256(__err_ptr, 28)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            if iszero(iszero(eq(outputCount, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645368617065282900000000)
                    let __err_hash := keccak256(__err_ptr, 28)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
                }
            }
            let oldVerifier := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
            let oldActive := and(shr(192, sload(mappingSlot(2, circuitId))), 255)
            if iszero(eq(oldVerifier, 0)) {
                let oldInputCount := and(shr(160, sload(mappingSlot(2, circuitId))), 65535)
                let oldOutputCount := and(shr(176, sload(mappingSlot(2, circuitId))), 65535)
                if iszero(eq(oldInputCount, inputCount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f757465725368617065496d6d757461626c6528290000)
                        let __err_hash := keccak256(__err_ptr, 30)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(eq(oldOutputCount, outputCount)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f757465725368617065496d6d757461626c6528290000)
                        let __err_hash := keccak256(__err_ptr, 30)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
            }
            let existingIdForVerifier := sload(mappingSlot(3, verifierAddr))
            if iszero(eq(existingIdForVerifier, 0)) {
                if iszero(eq(existingIdForVerifier, circuitId)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f757465724475706c6963617465566572696669657228)
                        mstore(add(__err_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 33)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
            }
            if iszero(eq(oldVerifier, 0)) {
                if iszero(eq(oldVerifier, verifierAddr)) {
                    sstore(mappingSlot(3, oldVerifier), 0)
                }
            }
            sstore(mappingSlot(3, verifierAddr), circuitId)
            {
                let __compat_value := verifierAddr
                let __compat_packed := and(__compat_value, 1461501637330902918203684832716283019655932542975)
                let __compat_slot_word := sload(mappingSlot(2, circuitId))
                let __compat_slot_cleared := and(__compat_slot_word, not(1461501637330902918203684832716283019655932542975))
                sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(0, __compat_packed)))
            }
            {
                let __compat_value := inputCount
                let __compat_packed := and(__compat_value, 65535)
                let __compat_slot_word := sload(mappingSlot(2, circuitId))
                let __compat_slot_cleared := and(__compat_slot_word, not(95779509802480722744478485512061607693151539203932160))
                sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(160, __compat_packed)))
            }
            {
                let __compat_value := outputCount
                let __compat_packed := and(__compat_value, 65535)
                let __compat_slot_word := sload(mappingSlot(2, circuitId))
                let __compat_slot_cleared := and(__compat_slot_word, not(6277005954415376645782142026518469521778379273268898037760))
                sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(176, __compat_packed)))
            }
            {
                let __compat_value := 1
                let __compat_packed := and(__compat_value, 255)
                let __compat_slot_word := sload(mappingSlot(2, circuitId))
                let __compat_slot_cleared := and(__compat_slot_word, not(1600660942523603594778126302917954936106100638338328800788480))
                sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(192, __compat_packed)))
            }
            {
                let __evt_ptr := mload(64)
                mstore(add(__evt_ptr, 0), 0x43697263756974526567697374657265642875696e743235362c616464726573)
                mstore(add(__evt_ptr, 32), 0x732c75696e743235362c75696e74323536290000000000000000000000000000)
                let __evt_topic0 := keccak256(__evt_ptr, 50)
                mstore(add(__evt_ptr, 0), and(verifierAddr, 0xffffffffffffffffffffffffffffffffffffffff))
                mstore(add(__evt_ptr, 32), inputCount)
                mstore(add(__evt_ptr, 64), outputCount)
                log2(__evt_ptr, 96, __evt_topic0, circuitId)
            }
            if iszero(eq(oldVerifier, 0)) {
                if eq(oldActive, 0) {
                    {
                        let __evt_ptr := mload(64)
                        mstore(add(__evt_ptr, 0), 0x436972637569744163746976655365742875696e743235362c75696e74323536)
                        mstore(add(__evt_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                        let __evt_topic0 := keccak256(__evt_ptr, 33)
                        mstore(add(__evt_ptr, 0), 1)
                        log2(__evt_ptr, 32, __evt_topic0, circuitId)
                    }
                }
            }
            stop()
        }
        function internal_internal_pauseCircuit(circuitId) {
            let sender := caller()
            let currentOwner := sload(0)
            if iszero(eq(sender, currentOwner)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                    mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 35)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 32
                    mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                    revert(0, add(4, __err_tail))
                }
            }
            let verifierAddr := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
            if iszero(iszero(eq(verifierAddr, 0))) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572556e6b6e6f776e436972637569742875696e)
                    mstore(add(__err_ptr, 32), 0x7432353629000000000000000000000000000000000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 37)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 32
                    mstore(4, circuitId)
                    revert(0, add(4, __err_tail))
                }
            }
            {
                let __compat_value := 0
                let __compat_packed := and(__compat_value, 255)
                let __compat_slot_word := sload(mappingSlot(2, circuitId))
                let __compat_slot_cleared := and(__compat_slot_word, not(1600660942523603594778126302917954936106100638338328800788480))
                sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(192, __compat_packed)))
            }
            {
                let __evt_ptr := mload(64)
                mstore(add(__evt_ptr, 0), 0x436972637569744163746976655365742875696e743235362c75696e74323536)
                mstore(add(__evt_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                let __evt_topic0 := keccak256(__evt_ptr, 33)
                mstore(add(__evt_ptr, 0), 0)
                log2(__evt_ptr, 32, __evt_topic0, circuitId)
            }
            stop()
        }
        function internal_internal_getCircuit(circuitId) -> __ret0, __ret1, __ret2, __ret3 {
            let verifierAddr := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
            let inputCount := and(shr(160, sload(mappingSlot(2, circuitId))), 65535)
            let outputCount := and(shr(176, sload(mappingSlot(2, circuitId))), 65535)
            let active := and(shr(192, sload(mappingSlot(2, circuitId))), 255)
            __ret0 := verifierAddr
            __ret1 := inputCount
            __ret2 := outputCount
            __ret3 := active
            leave
        }
        function internal_internal_verifierToCircuitId(verifierAddr) -> __ret0 {
            let circuitId := sload(mappingSlot(3, verifierAddr))
            __ret0 := circuitId
            leave
        }
        function internal_internal_renounceOwnership() {
            let sender := caller()
            let currentOwner := sload(0)
            if iszero(eq(sender, currentOwner)) {
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                    mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 35)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 32
                    mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                    revert(0, add(4, __err_tail))
                }
            }
            {
                let __err_ptr := mload(64)
                mstore(add(__err_ptr, 0), 0x5665726966696572526f7574657252656e6f756e63654f776e65727368697044)
                mstore(add(__err_ptr, 32), 0x697361626c656428290000000000000000000000000000000000000000000000)
                let __err_hash := keccak256(__err_ptr, 41)
                let __err_selector := shl(224, shr(224, __err_hash))
                mstore(0, __err_selector)
                let __err_tail := 0
                revert(0, add(4, __err_tail))
            }
            stop()
        }
        let sender := caller()
        sstore(0, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            function mappingSlot(baseSlot, key) -> slot {
                mstore(0, key)
                mstore(32, baseSlot)
                slot := keccak256(0, 64)
            }
            function internal_internal_owner() -> __ret0 {
                let current := sload(0)
                __ret0 := current
                leave
            }
            function internal_internal_pendingOwner() -> __ret0 {
                let pending := sload(1)
                __ret0 := pending
                leave
            }
            function internal_internal_transferOwnership(newOwner) {
                let sender := caller()
                let currentOwner := sload(0)
                if iszero(eq(sender, currentOwner)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                        mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 35)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 32
                        mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                        revert(0, add(4, __err_tail))
                    }
                }
                sstore(1, and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x4f776e6572736869705472616e73666572537461727465642861646472657373)
                    mstore(add(__evt_ptr, 32), 0x2c61646472657373290000000000000000000000000000000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 41)
                    log3(__evt_ptr, 0, __evt_topic0, and(currentOwner, 0xffffffffffffffffffffffffffffffffffffffff), and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
                }
                stop()
            }
            function internal_internal_acceptOwnership() {
                let sender := caller()
                let pending := sload(1)
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
                let previousOwner := sload(0)
                sstore(0, and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
                sstore(1, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x4f776e6572736869705472616e7366657272656428616464726573732c616464)
                    mstore(add(__evt_ptr, 32), 0x7265737329000000000000000000000000000000000000000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 37)
                    log3(__evt_ptr, 0, __evt_topic0, and(previousOwner, 0xffffffffffffffffffffffffffffffffffffffff), and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
                }
                stop()
            }
            function internal_internal_setCircuit(circuitId, verifierAddr, inputCount, outputCount) {
                let sender := caller()
                let currentOwner := sload(0)
                if iszero(eq(sender, currentOwner)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                        mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 35)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 32
                        mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(circuitId, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69644369726375697449642829)
                        let __err_hash := keccak256(__err_ptr, 32)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(verifierAddr, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645665726966696572282900)
                        let __err_hash := keccak256(__err_ptr, 31)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let codeLen := extcodesize(verifierAddr)
                if iszero(iszero(eq(codeLen, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645665726966696572282900)
                        let __err_hash := keccak256(__err_ptr, 31)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(inputCount, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645368617065282900000000)
                        let __err_hash := keccak256(__err_ptr, 28)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                if iszero(iszero(eq(outputCount, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645368617065282900000000)
                        let __err_hash := keccak256(__err_ptr, 28)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 0
                        revert(0, add(4, __err_tail))
                    }
                }
                let oldVerifier := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
                let oldActive := and(shr(192, sload(mappingSlot(2, circuitId))), 255)
                if iszero(eq(oldVerifier, 0)) {
                    let oldInputCount := and(shr(160, sload(mappingSlot(2, circuitId))), 65535)
                    let oldOutputCount := and(shr(176, sload(mappingSlot(2, circuitId))), 65535)
                    if iszero(eq(oldInputCount, inputCount)) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x5665726966696572526f757465725368617065496d6d757461626c6528290000)
                            let __err_hash := keccak256(__err_ptr, 30)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                    if iszero(eq(oldOutputCount, outputCount)) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x5665726966696572526f757465725368617065496d6d757461626c6528290000)
                            let __err_hash := keccak256(__err_ptr, 30)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                }
                let existingIdForVerifier := sload(mappingSlot(3, verifierAddr))
                if iszero(eq(existingIdForVerifier, 0)) {
                    if iszero(eq(existingIdForVerifier, circuitId)) {
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x5665726966696572526f757465724475706c6963617465566572696669657228)
                            mstore(add(__err_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                            let __err_hash := keccak256(__err_ptr, 33)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
                        }
                    }
                }
                if iszero(eq(oldVerifier, 0)) {
                    if iszero(eq(oldVerifier, verifierAddr)) {
                        sstore(mappingSlot(3, oldVerifier), 0)
                    }
                }
                sstore(mappingSlot(3, verifierAddr), circuitId)
                {
                    let __compat_value := verifierAddr
                    let __compat_packed := and(__compat_value, 1461501637330902918203684832716283019655932542975)
                    let __compat_slot_word := sload(mappingSlot(2, circuitId))
                    let __compat_slot_cleared := and(__compat_slot_word, not(1461501637330902918203684832716283019655932542975))
                    sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(0, __compat_packed)))
                }
                {
                    let __compat_value := inputCount
                    let __compat_packed := and(__compat_value, 65535)
                    let __compat_slot_word := sload(mappingSlot(2, circuitId))
                    let __compat_slot_cleared := and(__compat_slot_word, not(95779509802480722744478485512061607693151539203932160))
                    sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(160, __compat_packed)))
                }
                {
                    let __compat_value := outputCount
                    let __compat_packed := and(__compat_value, 65535)
                    let __compat_slot_word := sload(mappingSlot(2, circuitId))
                    let __compat_slot_cleared := and(__compat_slot_word, not(6277005954415376645782142026518469521778379273268898037760))
                    sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(176, __compat_packed)))
                }
                {
                    let __compat_value := 1
                    let __compat_packed := and(__compat_value, 255)
                    let __compat_slot_word := sload(mappingSlot(2, circuitId))
                    let __compat_slot_cleared := and(__compat_slot_word, not(1600660942523603594778126302917954936106100638338328800788480))
                    sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(192, __compat_packed)))
                }
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x43697263756974526567697374657265642875696e743235362c616464726573)
                    mstore(add(__evt_ptr, 32), 0x732c75696e743235362c75696e74323536290000000000000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 50)
                    mstore(add(__evt_ptr, 0), and(verifierAddr, 0xffffffffffffffffffffffffffffffffffffffff))
                    mstore(add(__evt_ptr, 32), inputCount)
                    mstore(add(__evt_ptr, 64), outputCount)
                    log2(__evt_ptr, 96, __evt_topic0, circuitId)
                }
                if iszero(eq(oldVerifier, 0)) {
                    if eq(oldActive, 0) {
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x436972637569744163746976655365742875696e743235362c75696e74323536)
                            mstore(add(__evt_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 33)
                            mstore(add(__evt_ptr, 0), 1)
                            log2(__evt_ptr, 32, __evt_topic0, circuitId)
                        }
                    }
                }
                stop()
            }
            function internal_internal_pauseCircuit(circuitId) {
                let sender := caller()
                let currentOwner := sload(0)
                if iszero(eq(sender, currentOwner)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                        mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 35)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 32
                        mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                        revert(0, add(4, __err_tail))
                    }
                }
                let verifierAddr := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
                if iszero(iszero(eq(verifierAddr, 0))) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572556e6b6e6f776e436972637569742875696e)
                        mstore(add(__err_ptr, 32), 0x7432353629000000000000000000000000000000000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 37)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 32
                        mstore(4, circuitId)
                        revert(0, add(4, __err_tail))
                    }
                }
                {
                    let __compat_value := 0
                    let __compat_packed := and(__compat_value, 255)
                    let __compat_slot_word := sload(mappingSlot(2, circuitId))
                    let __compat_slot_cleared := and(__compat_slot_word, not(1600660942523603594778126302917954936106100638338328800788480))
                    sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(192, __compat_packed)))
                }
                {
                    let __evt_ptr := mload(64)
                    mstore(add(__evt_ptr, 0), 0x436972637569744163746976655365742875696e743235362c75696e74323536)
                    mstore(add(__evt_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                    let __evt_topic0 := keccak256(__evt_ptr, 33)
                    mstore(add(__evt_ptr, 0), 0)
                    log2(__evt_ptr, 32, __evt_topic0, circuitId)
                }
                stop()
            }
            function internal_internal_getCircuit(circuitId) -> __ret0, __ret1, __ret2, __ret3 {
                let verifierAddr := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
                let inputCount := and(shr(160, sload(mappingSlot(2, circuitId))), 65535)
                let outputCount := and(shr(176, sload(mappingSlot(2, circuitId))), 65535)
                let active := and(shr(192, sload(mappingSlot(2, circuitId))), 255)
                __ret0 := verifierAddr
                __ret1 := inputCount
                __ret2 := outputCount
                __ret3 := active
                leave
            }
            function internal_internal_verifierToCircuitId(verifierAddr) -> __ret0 {
                let circuitId := sload(mappingSlot(3, verifierAddr))
                __ret0 := circuitId
                leave
            }
            function internal_internal_renounceOwnership() {
                let sender := caller()
                let currentOwner := sload(0)
                if iszero(eq(sender, currentOwner)) {
                    {
                        let __err_ptr := mload(64)
                        mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                        mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                        let __err_hash := keccak256(__err_ptr, 35)
                        let __err_selector := shl(224, shr(224, __err_hash))
                        mstore(0, __err_selector)
                        let __err_tail := 32
                        mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                        revert(0, add(4, __err_tail))
                    }
                }
                {
                    let __err_ptr := mload(64)
                    mstore(add(__err_ptr, 0), 0x5665726966696572526f7574657252656e6f756e63654f776e65727368697044)
                    mstore(add(__err_ptr, 32), 0x697361626c656428290000000000000000000000000000000000000000000000)
                    let __err_hash := keccak256(__err_ptr, 41)
                    let __err_selector := shl(224, shr(224, __err_hash))
                    mstore(0, __err_selector)
                    let __err_tail := 0
                    revert(0, add(4, __err_tail))
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
                    case 0x8da5cb5b {
                        /* owner() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        let current := sload(0)
                        mstore(0, current)
                        return(0, 32)
                    }
                    case 0xe30c3978 {
                        /* pendingOwner() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 4) {
                            revert(0, 0)
                        }
                        let pending := sload(1)
                        mstore(0, pending)
                        return(0, 32)
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
                        let sender := caller()
                        let currentOwner := sload(0)
                        if iszero(eq(sender, currentOwner)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                                mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 35)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 32
                                mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                                revert(0, add(4, __err_tail))
                            }
                        }
                        sstore(1, and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x4f776e6572736869705472616e73666572537461727465642861646472657373)
                            mstore(add(__evt_ptr, 32), 0x2c61646472657373290000000000000000000000000000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 41)
                            log3(__evt_ptr, 0, __evt_topic0, and(currentOwner, 0xffffffffffffffffffffffffffffffffffffffff), and(newOwner, 0xffffffffffffffffffffffffffffffffffffffff))
                        }
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
                        let pending := sload(1)
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
                        let previousOwner := sload(0)
                        sstore(0, and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
                        sstore(1, and(0, 0xffffffffffffffffffffffffffffffffffffffff))
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x4f776e6572736869705472616e7366657272656428616464726573732c616464)
                            mstore(add(__evt_ptr, 32), 0x7265737329000000000000000000000000000000000000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 37)
                            log3(__evt_ptr, 0, __evt_topic0, and(previousOwner, 0xffffffffffffffffffffffffffffffffffffffff), and(pending, 0xffffffffffffffffffffffffffffffffffffffff))
                        }
                        stop()
                    }
                    case 0xa3052a34 {
                        /* setCircuit() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 132) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 132) {
                            revert(0, 0)
                        }
                        let circuitId := calldataload(4)
                        let verifierAddr := and(calldataload(36), 0xffffffffffffffffffffffffffffffffffffffff)
                        let inputCount := calldataload(68)
                        let outputCount := calldataload(100)
                        let sender := caller()
                        let currentOwner := sload(0)
                        if iszero(eq(sender, currentOwner)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                                mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 35)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 32
                                mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(iszero(eq(circuitId, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69644369726375697449642829)
                                let __err_hash := keccak256(__err_ptr, 32)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(iszero(eq(verifierAddr, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645665726966696572282900)
                                let __err_hash := keccak256(__err_ptr, 31)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let codeLen := extcodesize(verifierAddr)
                        if iszero(iszero(eq(codeLen, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645665726966696572282900)
                                let __err_hash := keccak256(__err_ptr, 31)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(iszero(eq(inputCount, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645368617065282900000000)
                                let __err_hash := keccak256(__err_ptr, 28)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        if iszero(iszero(eq(outputCount, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572496e76616c69645368617065282900000000)
                                let __err_hash := keccak256(__err_ptr, 28)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 0
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let oldVerifier := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
                        let oldActive := and(shr(192, sload(mappingSlot(2, circuitId))), 255)
                        if iszero(eq(oldVerifier, 0)) {
                            let oldInputCount := and(shr(160, sload(mappingSlot(2, circuitId))), 65535)
                            let oldOutputCount := and(shr(176, sload(mappingSlot(2, circuitId))), 65535)
                            if iszero(eq(oldInputCount, inputCount)) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x5665726966696572526f757465725368617065496d6d757461626c6528290000)
                                    let __err_hash := keccak256(__err_ptr, 30)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                            if iszero(eq(oldOutputCount, outputCount)) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x5665726966696572526f757465725368617065496d6d757461626c6528290000)
                                    let __err_hash := keccak256(__err_ptr, 30)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                        }
                        let existingIdForVerifier := sload(mappingSlot(3, verifierAddr))
                        if iszero(eq(existingIdForVerifier, 0)) {
                            if iszero(eq(existingIdForVerifier, circuitId)) {
                                {
                                    let __err_ptr := mload(64)
                                    mstore(add(__err_ptr, 0), 0x5665726966696572526f757465724475706c6963617465566572696669657228)
                                    mstore(add(__err_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                                    let __err_hash := keccak256(__err_ptr, 33)
                                    let __err_selector := shl(224, shr(224, __err_hash))
                                    mstore(0, __err_selector)
                                    let __err_tail := 0
                                    revert(0, add(4, __err_tail))
                                }
                            }
                        }
                        if iszero(eq(oldVerifier, 0)) {
                            if iszero(eq(oldVerifier, verifierAddr)) {
                                sstore(mappingSlot(3, oldVerifier), 0)
                            }
                        }
                        sstore(mappingSlot(3, verifierAddr), circuitId)
                        {
                            let __compat_value := verifierAddr
                            let __compat_packed := and(__compat_value, 1461501637330902918203684832716283019655932542975)
                            let __compat_slot_word := sload(mappingSlot(2, circuitId))
                            let __compat_slot_cleared := and(__compat_slot_word, not(1461501637330902918203684832716283019655932542975))
                            sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(0, __compat_packed)))
                        }
                        {
                            let __compat_value := inputCount
                            let __compat_packed := and(__compat_value, 65535)
                            let __compat_slot_word := sload(mappingSlot(2, circuitId))
                            let __compat_slot_cleared := and(__compat_slot_word, not(95779509802480722744478485512061607693151539203932160))
                            sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(160, __compat_packed)))
                        }
                        {
                            let __compat_value := outputCount
                            let __compat_packed := and(__compat_value, 65535)
                            let __compat_slot_word := sload(mappingSlot(2, circuitId))
                            let __compat_slot_cleared := and(__compat_slot_word, not(6277005954415376645782142026518469521778379273268898037760))
                            sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(176, __compat_packed)))
                        }
                        {
                            let __compat_value := 1
                            let __compat_packed := and(__compat_value, 255)
                            let __compat_slot_word := sload(mappingSlot(2, circuitId))
                            let __compat_slot_cleared := and(__compat_slot_word, not(1600660942523603594778126302917954936106100638338328800788480))
                            sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(192, __compat_packed)))
                        }
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x43697263756974526567697374657265642875696e743235362c616464726573)
                            mstore(add(__evt_ptr, 32), 0x732c75696e743235362c75696e74323536290000000000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 50)
                            mstore(add(__evt_ptr, 0), and(verifierAddr, 0xffffffffffffffffffffffffffffffffffffffff))
                            mstore(add(__evt_ptr, 32), inputCount)
                            mstore(add(__evt_ptr, 64), outputCount)
                            log2(__evt_ptr, 96, __evt_topic0, circuitId)
                        }
                        if iszero(eq(oldVerifier, 0)) {
                            if eq(oldActive, 0) {
                                {
                                    let __evt_ptr := mload(64)
                                    mstore(add(__evt_ptr, 0), 0x436972637569744163746976655365742875696e743235362c75696e74323536)
                                    mstore(add(__evt_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                                    let __evt_topic0 := keccak256(__evt_ptr, 33)
                                    mstore(add(__evt_ptr, 0), 1)
                                    log2(__evt_ptr, 32, __evt_topic0, circuitId)
                                }
                            }
                        }
                        stop()
                    }
                    case 0xab088cac {
                        /* pauseCircuit() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let circuitId := calldataload(4)
                        let sender := caller()
                        let currentOwner := sload(0)
                        if iszero(eq(sender, currentOwner)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                                mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 35)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 32
                                mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                                revert(0, add(4, __err_tail))
                            }
                        }
                        let verifierAddr := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
                        if iszero(iszero(eq(verifierAddr, 0))) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x5665726966696572526f75746572556e6b6e6f776e436972637569742875696e)
                                mstore(add(__err_ptr, 32), 0x7432353629000000000000000000000000000000000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 37)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 32
                                mstore(4, circuitId)
                                revert(0, add(4, __err_tail))
                            }
                        }
                        {
                            let __compat_value := 0
                            let __compat_packed := and(__compat_value, 255)
                            let __compat_slot_word := sload(mappingSlot(2, circuitId))
                            let __compat_slot_cleared := and(__compat_slot_word, not(1600660942523603594778126302917954936106100638338328800788480))
                            sstore(mappingSlot(2, circuitId), or(__compat_slot_cleared, shl(192, __compat_packed)))
                        }
                        {
                            let __evt_ptr := mload(64)
                            mstore(add(__evt_ptr, 0), 0x436972637569744163746976655365742875696e743235362c75696e74323536)
                            mstore(add(__evt_ptr, 32), 0x2900000000000000000000000000000000000000000000000000000000000000)
                            let __evt_topic0 := keccak256(__evt_ptr, 33)
                            mstore(add(__evt_ptr, 0), 0)
                            log2(__evt_ptr, 32, __evt_topic0, circuitId)
                        }
                        stop()
                    }
                    case 0x88527fdd {
                        /* getCircuit() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let circuitId := calldataload(4)
                        let verifierAddr := and(shr(0, sload(mappingSlot(2, circuitId))), 1461501637330902918203684832716283019655932542975)
                        let inputCount := and(shr(160, sload(mappingSlot(2, circuitId))), 65535)
                        let outputCount := and(shr(176, sload(mappingSlot(2, circuitId))), 65535)
                        let active := and(shr(192, sload(mappingSlot(2, circuitId))), 255)
                        mstore(0, verifierAddr)
                        mstore(32, inputCount)
                        mstore(64, outputCount)
                        mstore(96, active)
                        return(0, 128)
                    }
                    case 0x576cae75 {
                        /* verifierToCircuitId() */
                        if callvalue() {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        if lt(calldatasize(), 36) {
                            revert(0, 0)
                        }
                        let verifierAddr := and(calldataload(4), 0xffffffffffffffffffffffffffffffffffffffff)
                        let circuitId := sload(mappingSlot(3, verifierAddr))
                        mstore(0, circuitId)
                        return(0, 32)
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
                        let sender := caller()
                        let currentOwner := sload(0)
                        if iszero(eq(sender, currentOwner)) {
                            {
                                let __err_ptr := mload(64)
                                mstore(add(__err_ptr, 0), 0x4f776e61626c65556e617574686f72697a65644163636f756e74286164647265)
                                mstore(add(__err_ptr, 32), 0x7373290000000000000000000000000000000000000000000000000000000000)
                                let __err_hash := keccak256(__err_ptr, 35)
                                let __err_selector := shl(224, shr(224, __err_hash))
                                mstore(0, __err_selector)
                                let __err_tail := 32
                                mstore(4, and(sender, 0xffffffffffffffffffffffffffffffffffffffff))
                                revert(0, add(4, __err_tail))
                            }
                        }
                        {
                            let __err_ptr := mload(64)
                            mstore(add(__err_ptr, 0), 0x5665726966696572526f7574657252656e6f756e63654f776e65727368697044)
                            mstore(add(__err_ptr, 32), 0x697361626c656428290000000000000000000000000000000000000000000000)
                            let __err_hash := keccak256(__err_ptr, 41)
                            let __err_selector := shl(224, shr(224, __err_hash))
                            mstore(0, __err_selector)
                            let __err_tail := 0
                            revert(0, add(4, __err_tail))
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