// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

/**
 * @title Raw error data holder contract
 */
abstract contract DeltaErrors {
    ////////////////////////////////////////////////////
    // Error data
    ////////////////////////////////////////////////////

    // the compiler should drop these since they are unused
    // but it should still be included in the ABI to parse the
    // errors below
    error Slippage();
    error NativeTransferFailed();
    error WrapFailed();
    error InvalidDex();
    error BadPool();
    error InvalidFlashLoan();
    error InvalidOperation();
    error InvalidCaller();
    error InvalidInitiator();
    error InvalidCalldata();
    error Target();
    error InvalidDexId();

    // Slippage()
    bytes4 internal constant SLIPPAGE = 0x7dd37f70;
    // NativeTransferFailed()
    bytes4 internal constant NATIVE_TRANSFER = 0xf4b3b1bc;
    // WrapFailed()
    bytes4 internal constant WRAP = 0xc30d93ce;
    // InvalidDex()
    bytes4 internal constant INVALID_DEX = 0x7948739e;
    // BadPool()
    bytes4 internal constant BAD_POOL = 0xb2c02722;
    // InvalidFlashLoan()
    bytes4 internal constant INVALID_FLASH_LOAN = 0xbafe1c53;
    // InvalidOperation()
    bytes4 internal constant INVALID_OPERATION = 0x398d4d32;
    // InvalidCaller()
    bytes4 internal constant INVALID_CALLER = 0x48f5c3ed;
    // InvalidInitiator()
    bytes4 internal constant INVALID_INITIATOR = 0xbfda1f28;
    // InvalidCalldata()
    bytes4 internal constant INVALID_CALLDATA = 0x8129bbcd;
    // Target()
    bytes4 internal constant INVALID_TARGET = 0x4fe6f55f;
    // InvalidDexId()
    bytes4 internal constant INVALID_DEX_ID = 0x0bbef348;

    function _invalidOperation() internal pure {
        assembly {
            mstore(0, INVALID_OPERATION)
            revert(0, 0x4)
        }
    }
}
