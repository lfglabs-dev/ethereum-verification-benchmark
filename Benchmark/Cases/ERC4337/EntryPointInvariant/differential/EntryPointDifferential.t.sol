// SPDX-License-Identifier: MIT
pragma solidity 0.8.28;

interface Vm {
    function envBytes(string calldata name) external returns (bytes memory value);
}

/// @notice Minimal subset of the PackedUserOperation struct as used by
/// EntryPoint v0.9.
struct PackedUserOperation {
    address sender;
    uint256 nonce;
    bytes initCode;
    bytes callData;
    bytes32 accountGasLimits;
    uint256 preVerificationGas;
    bytes32 gasFees;
    bytes paymasterAndData;
    bytes signature;
}

interface IEntryPoint {
    function handleOps(PackedUserOperation[] calldata ops, address payable beneficiary) external;
    function getNonce(address sender, uint192 key) external view returns (uint256);
    function depositTo(address account) external payable;
    function balanceOf(address account) external view returns (uint256);
}

/// @notice A minimal account that records the calldata it was invoked with.
contract RecordingAccount {
    bytes public lastCallData;
    address public lastCaller;
    uint256 public callCount;

    function validateUserOp(
        PackedUserOperation calldata,
        bytes32,
        uint256 missingAccountFunds
    ) external returns (uint256 validationData) {
        if (missingAccountFunds > 0) {
            (bool ok,) = msg.sender.call{value: missingAccountFunds}("");
            require(ok, "transfer");
        }
        return 0;
    }

    fallback() external payable {
        lastCallData = msg.data;
        lastCaller = msg.sender;
        callCount += 1;
    }

    receive() external payable {}
}

/// @notice A minimal account that always reverts on validation.
contract RejectingAccount {
    function validateUserOp(
        PackedUserOperation calldata,
        bytes32,
        uint256
    ) external pure returns (uint256) {
        return 1; // sentinel: SIG_VALIDATION_FAILED
    }
    fallback() external payable {}
    receive() external payable {}
}

/// @notice A malicious account that re-enters handleOps during validation.
contract ReentrantAccount {
    IEntryPoint public ep;
    bool public attempted;
    bool public reentryReverted;

    constructor(IEntryPoint _ep) {
        ep = _ep;
    }

    function validateUserOp(
        PackedUserOperation calldata op,
        bytes32,
        uint256
    ) external returns (uint256) {
        attempted = true;
        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = op;
        try ep.handleOps(ops, payable(address(this))) {
            reentryReverted = false;
        } catch {
            reentryReverted = true;
        }
        return 0;
    }
    fallback() external payable {}
    receive() external payable {}
}

/// @notice The differential test contract. Deploys two EntryPoint bytecodes
/// — the original solc-compiled one and the Verity-compiled one — and runs
/// the same scenarios against both, asserting equivalent observable
/// outcomes.
contract EntryPointDifferential {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    IEntryPoint solcEP;
    IEntryPoint verityEP;
    address constant BENEFICIARY = address(0xBEEF);

    function assertTrue(bool condition, string memory reason) internal pure {
        require(condition, reason);
    }

    function assertEq(uint256 left, uint256 right, string memory reason) internal pure {
        require(left == right, reason);
    }

    function assertEq(bool left, bool right, string memory reason) internal pure {
        require(left == right, reason);
    }

    function assertEq(bytes32 left, bytes32 right, string memory reason) internal pure {
        require(left == right, reason);
    }

    function setUp() public {
        bytes memory solcCode = vm.envBytes("SOLC_ENTRYPOINT_BYTECODE");
        bytes memory verityCode = vm.envBytes("VERITY_ENTRYPOINT_BYTECODE");
        address solcAddr;
        address verityAddr;
        assembly {
            solcAddr := create(0, add(solcCode, 0x20), mload(solcCode))
            verityAddr := create(0, add(verityCode, 0x20), mload(verityCode))
        }
        require(solcAddr != address(0), "deploy solc EP");
        require(verityAddr != address(0), "deploy verity EP");
        solcEP = IEntryPoint(solcAddr);
        verityEP = IEntryPoint(verityAddr);
    }

    function _baseOp(address sender, uint256 nonce, bytes memory callData)
        internal
        pure
        returns (PackedUserOperation memory)
    {
        return PackedUserOperation({
            sender: sender,
            nonce: nonce,
            initCode: hex"",
            callData: callData,
            accountGasLimits: bytes32(uint256(uint128(200000)) << 128 | uint128(100000)),
            preVerificationGas: 21000,
            gasFees: bytes32(uint256(uint128(1 gwei)) << 128 | uint128(1 gwei)),
            paymasterAndData: hex"",
            signature: hex""
        });
    }

    function testValidateAndExecuteSingleOp() public {
        RecordingAccount acc = new RecordingAccount();
        solcEP.depositTo{value: 1 ether}(address(acc));
        verityEP.depositTo{value: 1 ether}(address(acc));

        bytes memory callData = hex"deadbeef";
        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = _baseOp(address(acc), 0, callData);

        solcEP.handleOps(ops, payable(BENEFICIARY));
        bytes memory solcSeen = acc.lastCallData();
        uint256 solcCount = acc.callCount();

        // Reset for verity run.
        acc = new RecordingAccount();
        verityEP.depositTo{value: 1 ether}(address(acc));
        ops[0].sender = address(acc);
        verityEP.handleOps(ops, payable(BENEFICIARY));
        bytes memory verSeen = acc.lastCallData();
        uint256 verCount = acc.callCount();

        assertEq(solcCount, verCount, "exec call count differs");
        assertEq(keccak256(solcSeen), keccak256(verSeen), "exec calldata differs");
    }

    function testNonceReplayRejected() public {
        RecordingAccount acc = new RecordingAccount();
        solcEP.depositTo{value: 1 ether}(address(acc));
        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = _baseOp(address(acc), 0, hex"00");
        solcEP.handleOps(ops, payable(BENEFICIARY));

        bool solcReverted;
        try solcEP.handleOps(ops, payable(BENEFICIARY)) {
            solcReverted = false;
        } catch {
            solcReverted = true;
        }

        RecordingAccount acc2 = new RecordingAccount();
        verityEP.depositTo{value: 1 ether}(address(acc2));
        ops[0].sender = address(acc2);
        verityEP.handleOps(ops, payable(BENEFICIARY));
        bool verReverted;
        try verityEP.handleOps(ops, payable(BENEFICIARY)) {
            verReverted = false;
        } catch {
            verReverted = true;
        }
        assertEq(solcReverted, verReverted, "replay rejection differs");
        assertTrue(solcReverted, "solc should reject replay");
    }

    function testEmptyCallDataNoExec() public {
        RecordingAccount solcAcc = new RecordingAccount();
        RecordingAccount verAcc = new RecordingAccount();
        solcEP.depositTo{value: 1 ether}(address(solcAcc));
        verityEP.depositTo{value: 1 ether}(address(verAcc));

        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = _baseOp(address(solcAcc), 0, hex"");
        solcEP.handleOps(ops, payable(BENEFICIARY));
        ops[0].sender = address(verAcc);
        verityEP.handleOps(ops, payable(BENEFICIARY));

        assertEq(solcAcc.callCount(), 0, "solc emitted exec on empty callData");
        assertEq(verAcc.callCount(), 0, "verity emitted exec on empty callData");
    }

    function testReentrancyBlocked() public {
        ReentrantAccount solcAcc = new ReentrantAccount(solcEP);
        ReentrantAccount verAcc = new ReentrantAccount(verityEP);
        solcEP.depositTo{value: 1 ether}(address(solcAcc));
        verityEP.depositTo{value: 1 ether}(address(verAcc));

        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = _baseOp(address(solcAcc), 0, hex"00");
        solcEP.handleOps(ops, payable(BENEFICIARY));
        ops[0].sender = address(verAcc);
        verityEP.handleOps(ops, payable(BENEFICIARY));

        assertTrue(solcAcc.attempted(), "solc account didn't attempt reentry");
        assertTrue(verAcc.attempted(), "verity account didn't attempt reentry");
        assertTrue(solcAcc.reentryReverted(), "solc allowed reentry");
        assertTrue(verAcc.reentryReverted(), "verity allowed reentry");
    }
}
