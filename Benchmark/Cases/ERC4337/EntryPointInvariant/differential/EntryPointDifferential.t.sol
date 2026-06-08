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

/// @notice Flattened one-op projection exposed by the Verity model. The model
/// deliberately avoids dynamic calldata-array decoding; tests derive these
/// words from the same PackedUserOperation passed to upstream handleOps.
interface IEntryPointProjection {
    function handleOps(
        address sender,
        address paymaster,
        uint256 key,
        uint256 declaredNonce,
        address beneficiary,
        uint256 hasInitCode,
        uint256 hasCallData
    ) external;
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
    IEntryPointProjection public projection;
    bool public attempted;
    bool public reentryReverted;

    constructor(address target, bool useProjection) {
        if (useProjection) {
            projection = IEntryPointProjection(target);
        } else {
            ep = IEntryPoint(target);
        }
    }

    function validateUserOp(
        PackedUserOperation calldata op,
        bytes32,
        uint256
    ) external returns (uint256) {
        attempted = true;
        if (address(projection) != address(0)) {
            try projection.handleOps(address(this), address(0), 0, op.nonce, address(this), 0, 1) {
                reentryReverted = false;
            } catch {
                reentryReverted = true;
            }
        } else {
            PackedUserOperation[] memory ops = new PackedUserOperation[](1);
            ops[0] = op;
            try ep.handleOps(ops, payable(address(this))) {
                reentryReverted = false;
            } catch {
                reentryReverted = true;
            }
        }
        return 0;
    }

    function validateUserOp(uint256, uint256) external returns (uint256) {
        attempted = true;
        try projection.handleOps(address(this), address(0), 0, 0, address(this), 0, 1) {
            reentryReverted = false;
        } catch {
            reentryReverted = true;
        }
        return 0;
    }
    fallback() external payable {
        if (address(projection) != address(0) && !attempted) {
            attempted = true;
            try projection.handleOps(address(this), address(0), 0, 0, address(this), 0, 1) {
                reentryReverted = false;
            } catch {
                reentryReverted = true;
            }
        }
    }
    receive() external payable {}
}

/// @notice The differential test contract. Deploys two EntryPoint bytecodes
/// — the original solc-compiled one and the Verity-compiled one — and runs
/// the same scenarios against both, asserting equivalent observable
/// outcomes.
contract EntryPointDifferential {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    IEntryPoint solcEP;
    IEntryPointProjection verityEP;
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
        verityEP = IEntryPointProjection(verityAddr);
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

    function _runVerity(PackedUserOperation memory op, address beneficiary) internal {
        verityEP.handleOps(
            op.sender,
            address(0),
            0,
            op.nonce,
            beneficiary,
            op.initCode.length == 0 ? 0 : 1,
            op.callData.length == 0 ? 0 : 1
        );
    }

    function testValidateAndExecuteSingleOp() public {
        RecordingAccount acc = new RecordingAccount();
        solcEP.depositTo{value: 1 ether}(address(acc));

        bytes memory callData = hex"deadbeef";
        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = _baseOp(address(acc), 0, callData);

        solcEP.handleOps(ops, payable(BENEFICIARY));
        bytes memory solcSeen = acc.lastCallData();
        uint256 solcCount = acc.callCount();

        // Reset for verity run.
        acc = new RecordingAccount();
        ops[0].sender = address(acc);
        _runVerity(ops[0], BENEFICIARY);
        bytes memory veritySeen = acc.lastCallData();
        uint256 verityCount = acc.callCount();

        assertEq(solcCount, 1, "solc should execute once");
        assertTrue(solcSeen.length > 0, "solc calldata should be non-empty");
        assertEq(verityCount, 1, "verity projection should execute once");
        assertTrue(veritySeen.length > 0, "verity projection calldata should be non-empty");
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
        ops[0].sender = address(acc2);
        _runVerity(ops[0], BENEFICIARY);
        bool verReverted;
        try verityEP.handleOps(address(acc2), address(0), 0, ops[0].nonce, BENEFICIARY, 0, 1) {
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

        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = _baseOp(address(solcAcc), 0, hex"");
        solcEP.handleOps(ops, payable(BENEFICIARY));
        ops[0].sender = address(verAcc);
        _runVerity(ops[0], BENEFICIARY);

        assertEq(solcAcc.callCount(), 0, "solc emitted exec on empty callData");
        assertEq(verAcc.callCount(), 0, "verity emitted exec on empty callData");
    }

    function testReentrancyBlocked() public {
        ReentrantAccount solcAcc = new ReentrantAccount(address(solcEP), false);
        ReentrantAccount verAcc = new ReentrantAccount(address(verityEP), true);
        solcEP.depositTo{value: 1 ether}(address(solcAcc));

        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = _baseOp(address(solcAcc), 0, hex"00");
        solcEP.handleOps(ops, payable(BENEFICIARY));
        ops[0].sender = address(verAcc);
        _runVerity(ops[0], BENEFICIARY);

        assertTrue(solcAcc.attempted(), "solc account didn't attempt reentry");
        assertTrue(verAcc.attempted(), "verity account didn't attempt reentry");
        assertTrue(solcAcc.reentryReverted(), "solc allowed reentry");
        assertTrue(verAcc.reentryReverted(), "verity allowed reentry");
    }
}
