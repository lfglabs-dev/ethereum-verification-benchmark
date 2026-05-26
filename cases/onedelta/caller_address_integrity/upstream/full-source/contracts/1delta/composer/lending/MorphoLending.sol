// SPDX-License-Identifier: BUSL-1.1

pragma solidity ^0.8.28;

import {ERC20Selectors} from "../../shared/selectors/ERC20Selectors.sol";
import {Masks} from "../../shared/masks/Masks.sol";

/**
 * @notice Lending base contract that wraps Morpho Blue
 */
abstract contract MorphoLending is ERC20Selectors, Masks {
    /// @dev Constant MorphoB address
    // address internal constant MORPHO_BLUE = 0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb;

    /// @dev  position(...)
    bytes32 private constant MORPHO_POSITION = 0x93c5206200000000000000000000000000000000000000000000000000000000;

    /// @dev  market(...)
    bytes32 private constant MORPHO_MARKET = 0x5c60e39a00000000000000000000000000000000000000000000000000000000;

    /// @dev  repay(...)
    bytes32 private constant MORPHO_REPAY = 0x20b76e8100000000000000000000000000000000000000000000000000000000;

    /// @dev  supplyCollateral(...)
    bytes32 private constant MORPHO_SUPPLY_COLLATERAL = 0x238d657900000000000000000000000000000000000000000000000000000000;

    /// @dev  supply(...)
    bytes32 private constant MORPHO_SUPPLY = 0xa99aad8900000000000000000000000000000000000000000000000000000000;

    /// @dev  borrow(...)
    bytes32 private constant MORPHO_BORROW = 0x50d8cd4b00000000000000000000000000000000000000000000000000000000;

    /// @dev  withdrawCollateral(...)
    bytes32 private constant MORPHO_WITHDRAW_COLLATERAL = 0x8720316d00000000000000000000000000000000000000000000000000000000;

    /**
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | MarketParams.loanToken          |
     * | 20     | 20             | MarketParams.collateralToken    |
     * | 40     | 20             | MarketParams.oracle             |
     * | 60     | 20             | MarketParams.irm                |
     * | 80     | 16             | MarketParams.lltv               |
     * | 96     |  1             | Assets or Shares                |
     * | 97     | 15             | Amount (borrowAm)               |
     * | 112    | 20             | receiver                        |
     * | 132    | 20             | morpho                          | <-- we allow all morphos (incl forks)
     */
    function _morphoBorrow(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            // morpho should be the primary choice
            let ptr := mload(0x40)

            // borrow(...)
            mstore(ptr, MORPHO_BORROW)

            // market data
            mstore(add(ptr, 4), shr(96, calldataload(currentOffset))) // MarketParams.loanToken
            mstore(add(ptr, 36), shr(96, calldataload(add(currentOffset, 20)))) // MarketParams.collateralToken
            mstore(add(ptr, 68), shr(96, calldataload(add(currentOffset, 40)))) // MarketParams.oracle
            mstore(add(ptr, 100), shr(96, calldataload(add(currentOffset, 60)))) // MarketParams.irm

            let lltvAndAmount := calldataload(add(currentOffset, 80))
            mstore(add(ptr, 132), shr(128, lltvAndAmount)) // MarketParams.lltv

            let borrowAm := and(UINT112_MASK, lltvAndAmount)

            /**
             * check if it is by shares or assets
             */
            switch and(USE_SHARES_FLAG, lltvAndAmount)
            case 0 {
                mstore(add(ptr, 164), borrowAm) // assets
                mstore(add(ptr, 196), 0) // shares
            }
            default {
                mstore(add(ptr, 164), 0) // assets
                mstore(add(ptr, 196), borrowAm) // shares
            }

            // onbehalf
            mstore(add(ptr, 228), callerAddress) // onBehalfOf
            let lastBit := calldataload(add(currentOffset, 112))
            mstore(add(ptr, 260), shr(96, lastBit)) // receiver
            let morpho := shr(96, calldataload(add(currentOffset, 132)))

            currentOffset := add(currentOffset, 152)
            if iszero(
                call(
                    gas(),
                    morpho,
                    0x0,
                    ptr,
                    292, // = 9 * 32 + 4
                    0x0,
                    0x0 //
                )
            ) {
                let rdlen := returndatasize()
                returndatacopy(0, 0, rdlen)
                revert(0x0, rdlen)
            }
        }

        return currentOffset;
    }

    /**
     * This deposits LENDING TOKEN
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | MarketParams.loanToken          |
     * | 20     | 20             | MarketParams.collateralToken    |
     * | 40     | 20             | MarketParams.oracle             |
     * | 60     | 20             | MarketParams.irm                |
     * | 80     | 16             | MarketParams.lltv               |
     * | 96     |  1             | Assets or Shares                |
     * | 97     | 15             | Amount (depositAm)              |
     * | 112    | 20             | receiver                        |
     * | 132    | 20             | morpho                          | <-- we allow all morphos (incl forks)
     * | 152    | 2              | calldataLength                  |
     * | 154    | calldataLength | calldata                        |
     */
    function _encodeMorphoDeposit(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            let ptrBase := mload(0x40)
            let ptr := add(128, ptrBase)

            // loan token
            let token := shr(96, calldataload(currentOffset))

            // supply(...)
            mstore(ptr, MORPHO_SUPPLY)
            // market data
            mstore(add(ptr, 4), token) // MarketParams.loanToken
            mstore(add(ptr, 36), shr(96, calldataload(add(currentOffset, 20)))) // MarketParams.collateralToken
            mstore(add(ptr, 68), shr(96, calldataload(add(currentOffset, 40)))) // MarketParams.oracle
            mstore(add(ptr, 100), shr(96, calldataload(add(currentOffset, 60)))) // MarketParams.irm

            let lltvAndAmount := calldataload(add(currentOffset, 80))
            mstore(add(ptr, 132), shr(128, lltvAndAmount)) // MarketParams.lltv
            let amountToDeposit := and(UINT112_MASK, lltvAndAmount)
            // increment for the amounts

            /**
             * check if it is by shares or assets
             */
            switch and(USE_SHARES_FLAG, lltvAndAmount)
            case 0 {
                /**
                 * if the amount is zero, we assume that the contract balance is deposited
                 */
                if iszero(amountToDeposit) {
                    // selector for balanceOf(address)
                    mstore(0, ERC20_BALANCE_OF)
                    // add this address as parameter
                    mstore(0x04, address())
                    // call to token
                    pop(staticcall(gas(), token, 0x0, 0x24, 0x0, 0x20))
                    // load the retrieved balance
                    amountToDeposit := mload(0x0)
                }

                mstore(add(ptr, 164), amountToDeposit) // assets
                mstore(add(ptr, 196), 0) // shares
            }
            default {
                mstore(add(ptr, 164), 0) // assets
                mstore(add(ptr, 196), amountToDeposit) // shares
            }

            // receiver address
            let receiver := shr(96, calldataload(add(currentOffset, 112)))

            let morpho := shr(96, calldataload(add(currentOffset, 132)))

            // get calldatalength
            let inputCalldataLength := and(UINT16_MASK, shr(240, calldataload(add(currentOffset, 152))))
            let calldataLength := inputCalldataLength

            currentOffset := add(currentOffset, 154)

            // leftover params
            mstore(add(ptr, 228), receiver) // onBehalfOf is the receiver here
            mstore(add(ptr, 260), 0x120) // offset
            // add calldata if needed
            if xor(0, calldataLength) {
                calldataLength := add(calldataLength, 20)
                mstore(add(ptr, 324), shl(96, callerAddress)) // caller
                calldatacopy(add(ptr, 344), currentOffset, inputCalldataLength) // calldata
                currentOffset := add(currentOffset, inputCalldataLength)
            }

            mstore(add(ptr, 292), calldataLength) // calldatalength

            if iszero(
                call(
                    gas(),
                    morpho,
                    0x0,
                    ptr,
                    add(calldataLength, 324), // = 10 * 32 + 4
                    0x0,
                    0x0 //
                )
            ) {
                let rdlen := returndatasize()
                returndatacopy(0, 0, rdlen)
                revert(0x0, rdlen)
            }
        }
        return currentOffset;
    }

    /**
     * This deposits COLLATERAL - never uses shares
     * | Offset | Length (bytes) | Description                     |
     * |--------|----------------|---------------------------------|
     * | 0      | 20             | MarketParams.loanToken          |
     * | 20     | 20             | MarketParams.collateralToken    |
     * | 40     | 20             | MarketParams.oracle             |
     * | 60     | 20             | MarketParams.irm                |
     * | 80     | 16             | MarketParams.lltv               |
     * | 96     | 16             | Amount (depositAm)              |
     * | 112    | 20             | receiver                        |
     * | 132    | 20             | morpho                          | <-- we allow all morphos (incl forks)
     * | 152    | 2              | calldataLength                  |
     * | 154    | calldataLength | calldata                        |
     */
    function _encodeMorphoDepositCollateral(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            // use two memory ranges
            let ptrBase := mload(0x40)
            let ptr := add(256, ptrBase)

            // supplyCollateral(...)
            mstore(ptr, MORPHO_SUPPLY_COLLATERAL)
            mstore(add(ptr, 4), shr(96, calldataload(currentOffset))) // MarketParams.loanToken

            // get the collateral token and approve if needed
            let token := shr(96, calldataload(add(currentOffset, 20)))
            mstore(add(ptr, 36), token) // MarketParams.collateralToken
            mstore(add(ptr, 68), shr(96, calldataload(add(currentOffset, 40)))) // MarketParams.oracle
            mstore(add(ptr, 100), shr(96, calldataload(add(currentOffset, 60)))) // MarketParams.irm
            let lltvAndAmount := calldataload(add(currentOffset, 80))
            mstore(add(ptr, 132), shr(128, lltvAndAmount)) // MarketParams.lltv

            // we ignore flags as this only allows assets
            let amountToDeposit := and(UINT120_MASK, lltvAndAmount)

            /**
             * if the amount is zero, we assume that the contract balance is deposited
             */
            if iszero(amountToDeposit) {
                // selector for balanceOf(address)
                mstore(0, ERC20_BALANCE_OF)
                // add this address as parameter
                mstore(0x04, address())
                // call to token
                pop(staticcall(gas(), token, 0x0, 0x24, 0x0, 0x20))
                // load the retrieved balance
                amountToDeposit := mload(0x0)
            }

            // receiver address
            let receiver := shr(96, calldataload(add(currentOffset, 112)))

            mstore(add(ptr, 164), amountToDeposit) // assets
            mstore(add(ptr, 196), receiver) // onBehalfOf
            mstore(add(ptr, 228), 0x100) // offset

            // get morpho
            let morpho := shr(96, calldataload(add(currentOffset, 132)))

            // get calldatalength
            let inputCalldataLength := and(UINT16_MASK, shr(240, calldataload(add(currentOffset, 152))))
            let calldataLength := inputCalldataLength
            currentOffset := add(currentOffset, 154)

            // add calldata if needed
            if xor(0, calldataLength) {
                calldataLength := add(calldataLength, 20)
                mstore(add(ptr, 292), shl(96, callerAddress)) // caller
                calldatacopy(add(ptr, 312), currentOffset, inputCalldataLength) // calldata
                currentOffset := add(currentOffset, inputCalldataLength)
            }

            mstore(add(ptr, 260), calldataLength) // calldatalength
            if iszero(
                call(
                    gas(),
                    morpho,
                    0x0,
                    ptr,
                    add(calldataLength, 292), // = 10 * 32 + 4
                    0x0,
                    0x0 //
                )
            ) {
                let rdlen := returndatasize()
                returndatacopy(0, 0, rdlen)
                revert(0x0, rdlen)
            }
        }
        return currentOffset;
    }

    /// @notice Withdraw collateral from Morpho Blue
    function _encodeMorphoWithdrawCollateral(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            // morpho should be the primary choice
            let ptr := mload(0x40)

            // withdrawCollateral(...)
            mstore(ptr, MORPHO_WITHDRAW_COLLATERAL)

            // market stuff

            mstore(add(ptr, 4), shr(96, calldataload(currentOffset))) // MarketParams.loanToken
            mstore(add(ptr, 36), shr(96, calldataload(add(currentOffset, 20)))) // MarketParams.collateralToken
            mstore(add(ptr, 68), shr(96, calldataload(add(currentOffset, 40)))) // MarketParams.oracle
            mstore(add(ptr, 100), shr(96, calldataload(add(currentOffset, 60)))) // MarketParams.irm

            let lltvAndAmount := calldataload(add(currentOffset, 80))

            mstore(add(ptr, 132), shr(128, lltvAndAmount)) // MarketParams.lltv

            mstore(add(ptr, 196), callerAddress) // onBehalfOf

            // store receiver
            mstore(add(ptr, 228), shr(96, calldataload(add(currentOffset, 112)))) // receiver
            // skip receiver in offset

            let morpho := shr(96, calldataload(add(currentOffset, 132)))

            // get amount, ignore flags
            lltvAndAmount := and(UINT120_MASK, lltvAndAmount)

            // technically not needed, hwoever, we keep it consistent
            // to withdraw all like this - maxUnit112 means read collateral balance
            if eq(lltvAndAmount, 0xffffffffffffffffffffffffffff) {
                let ptrBase := add(ptr, 280)
                let marketId := keccak256(add(ptr, 4), 160)
                // position datas (1st slot of return data is the user shares)
                mstore(ptrBase, MORPHO_POSITION)
                mstore(add(ptrBase, 0x4), marketId)
                mstore(add(ptrBase, 0x24), callerAddress)
                if iszero(staticcall(gas(), morpho, ptrBase, 0x44, ptrBase, 0x60)) { revert(0x0, 0x0) }
                lltvAndAmount := mload(add(ptrBase, 0x40))
            }

            // amount is stored last
            mstore(add(ptr, 164), lltvAndAmount) // assets

            currentOffset := add(currentOffset, 152)

            if iszero(
                call(
                    gas(),
                    morpho,
                    0x0,
                    ptr,
                    260, // = 8 * 32 + 4
                    0x0,
                    0x0 //
                )
            ) {
                let rdlen := returndatasize()
                returndatacopy(0, 0, rdlen)
                revert(0x0, rdlen)
            }
        }
        return currentOffset;
    }

    /// @notice Withdraw borrowAsset from Morpho
    function _encodeMorphoWithdraw(uint256 currentOffset, address callerAddress) internal returns (uint256) {
        assembly {
            // morpho should be the primary choice
            let ptrBase := mload(0x40)
            let ptr := add(ptrBase, 256)

            // market data
            mstore(add(ptr, 4), shr(96, calldataload(currentOffset))) // MarketParams.loanToken
            mstore(add(ptr, 36), shr(96, calldataload(add(currentOffset, 20)))) // MarketParams.collateralToken
            mstore(add(ptr, 68), shr(96, calldataload(add(currentOffset, 40)))) // MarketParams.oracle
            mstore(add(ptr, 100), shr(96, calldataload(add(currentOffset, 60)))) // MarketParams.irm
            let lltvAndAmount := calldataload(add(currentOffset, 80))
            mstore(add(ptr, 132), shr(128, lltvAndAmount)) // MarketParams.lltv

            let withdrawAm := and(UINT120_MASK, lltvAndAmount)

            mstore(add(ptr, 228), callerAddress) // onBehalfOf
            mstore(add(ptr, 260), shr(96, calldataload(add(currentOffset, 112)))) // receiver
            // get morpho
            let morpho := shr(96, calldataload(add(currentOffset, 132)))
            currentOffset := add(currentOffset, 152)

            /**
             * check if it is by shares or assets
             * 0 => by assets
             * 1 => by shares
             */
            switch and(USE_SHARES_FLAG, lltvAndAmount)
            case 0 {
                /**
                 * Withdraw amount variations
                 * type(uint120).max:    user supply balance
                 * other:                amount provided
                 */
                switch withdrawAm
                // maximum uint112 means withdraw everything
                case 0xffffffffffffffffffffffffffff {
                    // we need to fetch user shares and just withdraw all shares
                    // https://docs.morpho.org/morpho/tutorials/manage-positions/#repayAll

                    let marketId := keccak256(add(ptr, 4), 160)
                    // position datas (1st slot of return data is the user shares)
                    mstore(ptrBase, MORPHO_POSITION)
                    mstore(add(ptrBase, 0x4), marketId)
                    mstore(add(ptrBase, 0x24), callerAddress)
                    if iszero(staticcall(gas(), morpho, ptrBase, 0x44, ptrBase, 0x20)) { revert(0x0, 0x0) }
                    mstore(add(ptr, 164), 0) // assets
                    mstore(add(ptr, 196), mload(ptrBase)) // shares
                }
                // explicit amount
                default {
                    mstore(add(ptr, 164), withdrawAm) // assets
                    mstore(add(ptr, 196), 0) // shares
                }
            }
            default {
                mstore(add(ptr, 164), 0) // assets
                mstore(add(ptr, 196), withdrawAm) // shares
            }

            // withdraw(...)
            // we have to do it like this to override the selector only in this memory position
            mstore(sub(ptr, 28), 0x5c2bea49)
            if iszero(
                call(
                    gas(),
                    morpho,
                    0x0,
                    ptr,
                    292, // = 9 * 32 + 4
                    0x0,
                    0x0 //
                )
            ) {
                let rdlen := returndatasize()
                returndatacopy(0, 0, rdlen)
                revert(0x0, rdlen)
            }
        }
        return currentOffset;
    }

    /// @notice Repay to morpho blue
    function _morphoRepay(
        uint256 currentOffset,
        address callerAddress
    )
        internal
        returns (
            // this will be returned as the offset, but initialized as lltvAndAmount
            // we use it here to avoid stack-too deep
            uint256 tempData
        )
    {
        assembly {
            // morpho should be the primary choice
            let ptrBase := mload(0x40)
            let ptr := add(ptrBase, 256)

            let token := shr(96, calldataload(currentOffset))
            // market data
            mstore(add(ptr, 4), token) // MarketParams.loanToken
            mstore(add(ptr, 36), shr(96, calldataload(add(currentOffset, 20)))) // MarketParams.collateralToken
            mstore(add(ptr, 68), shr(96, calldataload(add(currentOffset, 40)))) // MarketParams.oracle
            mstore(add(ptr, 100), shr(96, calldataload(add(currentOffset, 60)))) // MarketParams.irm
            tempData := calldataload(add(currentOffset, 80))
            mstore(add(ptr, 132), shr(128, tempData)) // MarketParams.lltv

            let repayAm := and(UINT120_MASK, tempData)
            // skip amounts

            // receiver address
            let receiver := shr(96, calldataload(add(currentOffset, 112)))

            let morpho := shr(96, calldataload(add(currentOffset, 132)))

            /**
             *  if repayAmount is Max -> repay safe maximum (to prevent too low contract balance to revert)
             *  else if repayAmount is 0 -> repay contract balance as assets
             *  else repay amount as shares or assets, based on flag set
             */
            switch repayAm
            case 0xffffffffffffffffffffffffffff {
                // get the contract balance
                mstore(0x0, ERC20_BALANCE_OF)
                mstore(0x04, address())
                if iszero(staticcall(gas(), token, 0x0, 0x24, 0x0, 0x20)) { revert(0x0, 0x0) }
                // this is the maximum we can repay
                repayAm := mload(0x0)

                // by assets safe - will not revert if too much is repaid
                // we need to fetch everything and acrure interest
                // https://docs.morpho.org/morpho/tutorials/manage-positions/#repayAll

                // accrue interest
                // add accrueInterest (0x151c1ade)
                mstore(sub(ptr, 28), 0x151c1ade)
                if iszero(call(gas(), morpho, 0x0, ptr, 0xA4, 0x0, 0x0)) { revert(0x0, 0x0) }

                // get market params for conversion
                let marketId := keccak256(add(ptr, 4), 160)
                mstore(0x0, MORPHO_MARKET)
                mstore(0x4, marketId)
                if iszero(staticcall(gas(), morpho, 0x0, 0x24, ptrBase, 0x80)) { revert(0x0, 0x0) }
                let totalBorrowAssets := mload(add(ptrBase, 0x40))
                let totalBorrowShares := mload(add(ptrBase, 0x60))

                // position datas
                mstore(ptrBase, MORPHO_POSITION)
                mstore(add(ptrBase, 0x4), marketId)
                mstore(add(ptrBase, 0x24), receiver)
                if iszero(staticcall(gas(), morpho, ptrBase, 0x44, ptrBase, 0x40)) { revert(0x0, 0x0) }
                let userBorrowShares := mload(add(ptrBase, 0x20))

                // mulDivUp(shares, totalAssets + VIRTUAL_ASSETS, totalShares + VIRTUAL_SHARES);
                let maxAssets := add(totalBorrowShares, 1000000) // VIRTUAL_SHARES=1e6
                maxAssets :=
                    div(
                        add(
                            mul(userBorrowShares, add(totalBorrowAssets, 1)), // VIRTUAL_ASSETS=1
                            sub(maxAssets, 1) //
                        ),
                        maxAssets //
                    )

                // if maxAssets is greater than repay amount
                // we repay whatever is possible
                switch gt(maxAssets, repayAm)
                case 1 {
                    mstore(add(ptr, 164), repayAm) // assets
                    mstore(add(ptr, 196), 0) // shares
                }
                // otherwise, repay all shares, leaving no dust
                default {
                    mstore(add(ptr, 164), 0) // assets
                    mstore(add(ptr, 196), userBorrowShares) // shares
                }
            }
            // by balance (using assets)
            case 0 {
                // get balance
                mstore(0x0, ERC20_BALANCE_OF)
                mstore(0x04, address())
                if iszero(staticcall(gas(), token, 0x0, 0x24, 0x0, 0x20)) { revert(0x0, 0x0) }

                // use balance by assets
                mstore(add(ptr, 164), mload(0x0)) // assets
                mstore(add(ptr, 196), 0) // shares
            }
            // plain amount (assets or shares)
            default {
                switch and(USE_SHARES_FLAG, tempData)
                case 0 {
                    // by assets
                    mstore(add(ptr, 164), repayAm) // assets
                    mstore(add(ptr, 196), 0) // shares
                }
                default {
                    // by shares
                    mstore(add(ptr, 164), 0) // assets
                    mstore(add(ptr, 196), repayAm) // shares
                }
            }

            mstore(add(ptr, 228), receiver) // onBehalfOf is the receiver here
            mstore(add(ptr, 260), 0x120) // offset

            // get calldatalength
            let inputCalldataLength := and(UINT16_MASK, shr(240, calldataload(add(currentOffset, 152))))
            let calldataLength := inputCalldataLength
            currentOffset := add(currentOffset, 154)

            // add calldata if needed
            if xor(0, calldataLength) {
                calldataLength := add(calldataLength, 20)
                mstore(add(ptr, 324), shl(96, callerAddress)) // caller
                calldatacopy(add(ptr, 344), currentOffset, inputCalldataLength) // calldata
                currentOffset := add(currentOffset, inputCalldataLength)
            }

            // repay(...)
            // we have to do it like this to override the selector only in this memory position
            mstore(sub(ptr, 28), 0x20b76e81)
            mstore(add(ptr, 292), calldataLength) // calldatalength
            if iszero(
                call(
                    gas(),
                    morpho,
                    0x0,
                    ptr,
                    add(calldataLength, 324), // = 10 * 32 + 4
                    0x0,
                    0x0 //
                )
            ) {
                let rdlen := returndatasize()
                returndatacopy(0, 0, rdlen)
                revert(0x0, rdlen)
            }
        }
        return currentOffset;
    }
}
