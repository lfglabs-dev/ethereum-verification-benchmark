// SPDX-License-Identifier: BUSL-1.1

pragma solidity 0.8.28;

import {Masks} from "../../../../../shared/masks/Masks.sol";
import {DeltaErrors} from "../../../../../shared/errors/Errors.sol";

/**
 * @title Take an Aave v3 flash loan callback
 */
contract AaveV3FlashLoanCallback is Masks, DeltaErrors {
    // Aave V3 style lender pool addresses
    address private constant AAVE_V3 = 0x87870Bca3F3fD6335C3F4ce8392D69350B4fA4E2;
    address private constant AAVE_V3_PRIME = 0x4e033931ad43597d96D6bcc25c280717730B58B1;
    address private constant AAVE_V3_ETHER_FI = 0x0AA97c284e98396202b6A04024F5E2c65026F3c0;
    address private constant AAVE_V3_HORIZON = 0xAe05Cd22df81871bc7cC2a04BeCfb516bFe332C8;
    address private constant SPARK = 0xC13e21B648A5Ee794902342038FF3aDAB66BE987;
    address private constant ZEROLEND_STABLECOINS_RWA = 0xD3a4DA66EC15a001466F324FA08037f3272BDbE8;
    address private constant ZEROLEND_ETH_LRTS = 0x3BC3D34C32cc98bf098D832364Df8A222bBaB4c0;
    address private constant ZEROLEND_BTC_LRTS = 0xCD2b31071119D7eA449a9D211AC8eBF7Ee97F987;
    address private constant AVALON_SOLVBTC = 0x35B3F1BFe7cbE1e95A3DC2Ad054eB6f0D4c879b6;
    address private constant AVALON_SWELLBTC = 0xE0E468687703dD02BEFfB0BE13cFB109529F38e0;
    address private constant AVALON_PUMPBTC = 0x1c8091b280650aFc454939450699ECAA67C902d9;
    address private constant AVALON_EBTC_LBTC = 0xCfe357D2dE5aa5dAB5fEf255c911D150d0246423;
    address private constant KINZA = 0xeA14474946C59Dee1F103aD517132B3F19Cef1bE;
    address private constant YLDR = 0x6447c4390457CaD03Ec1BaA4254CEe1A3D9e1Bbd;

    /**
     * @dev Aave V3 style flash loan callback
     */
    function executeOperation(
        address,
        uint256,
        uint256,
        address initiator,
        bytes calldata params // user params
    )
        external
        returns (bool)
    {
        address origCaller;
        uint256 calldataLength;
        assembly {
            calldataLength := params.length

            // validate caller
            // - extract id from params
            let firstWord := calldataload(196)

            // We check that the caller is one of the lending pools
            // This is a crucial check since this makes
            // the initiator paramter the caller of flashLoan
            let pool
            let poolId := and(UINT8_MASK, shr(88, firstWord))

            switch lt(poolId, 4)
            case 1 {
                switch poolId
                case 0 { pool := AAVE_V3 }
                case 1 { pool := AAVE_V3_PRIME }
                case 2 { pool := AAVE_V3_ETHER_FI }
                case 3 { pool := AAVE_V3_HORIZON }
            }
            default {
                switch lt(poolId, 24)
                case 1 {
                    switch poolId
                    case 10 { pool := SPARK }
                    case 21 { pool := ZEROLEND_STABLECOINS_RWA }
                    case 22 { pool := ZEROLEND_ETH_LRTS }
                    case 23 { pool := ZEROLEND_BTC_LRTS }
                }
                default {
                    switch poolId
                    case 51 { pool := AVALON_SOLVBTC }
                    case 52 { pool := AVALON_SWELLBTC }
                    case 53 { pool := AVALON_PUMPBTC }
                    case 54 { pool := AVALON_EBTC_LBTC }
                    case 82 { pool := KINZA }
                    case 100 { pool := YLDR }
                }
            }

            // catch unassigned pool / bad poolId
            if iszero(pool) {
                mstore(0, INVALID_FLASH_LOAN)
                revert(0, 0x4)
            }
            // match pool address
            if xor(caller(), pool) {
                mstore(0, INVALID_CALLER)
                revert(0, 0x4)
            }

            // We require to self-initiate
            // this prevents caller impersonation,
            // but ONLY if the caller address is
            // an Aave V3 type lending pool
            if xor(address(), initiator) {
                mstore(0, INVALID_INITIATOR)
                revert(0, 0x4)
            }
            // Slice the original caller off the beginnig of the calldata
            // From here on we have validated that the origCaller
            // was attached in the deltaCompose function
            // Otherwise, this would be a vulnerability
            origCaller := shr(96, firstWord)
            // shift / slice params
            calldataLength := sub(calldataLength, 21)
        }
        // within the flash loan, any compose operation
        // can be executed
        _deltaComposeInternal(
            origCaller,
            217, // 196 +21 as constant offset
            calldataLength
        );
        return true;
    }

    function _deltaComposeInternal(address callerAddress, uint256 offset, uint256 length) internal virtual {}
}
