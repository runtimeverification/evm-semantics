// SPDX-License-Identifier: MIT
pragma solidity >=0.6.2 <0.9.0;
pragma experimental ABIEncoderV2;

interface KEVMCheatsBase {
    // Expects a call using the CALL opcode to an address with the specified calldata.
    function expectRegularCall(address,bytes calldata) external;
    // Expects a call using the CALL opcode to an address with the specified msg.value and calldata.
    function expectRegularCall(address,uint256,bytes calldata) external;
    // Expects a static call to an address with the specified calldata.
    function expectStaticCall(address,bytes calldata) external;
    // Expects a delegate call to an address with the specified calldata.
    function expectDelegateCall(address,bytes calldata) external;
    // Expects that no contract calls are made after invoking the cheatcode.
    function expectNoCall() external;
    // Expects the given address to deploy a new contract, using the CREATE opcode, with the specified value and bytecode.
    function expectCreate(address,uint256,bytes calldata) external;
    // Expects the given address to deploy a new contract, using the CREATE2 opcode, with the specified value and bytecode (appended with a bytes32 salt).
    function expectCreate2(address,uint256,bytes calldata) external;
    // Makes the storage of the given address completely symbolic.
    function symbolicStorage(address) external;
    // Adds an address to the whitelist.
    function allowCallsToAddress(address) external;
    // Adds an address and a storage slot to the whitelist.
    function allowChangesToStorage(address,uint256) external;
    // Set the current <gas> cell
    function infiniteGas() external;
    // Returns a symbolic unsigned integer
    function freshUInt(uint8) external returns (uint256);
    // Returns a symbolic boolean value
    function freshBool() external returns (uint256);
}

abstract contract SymbolicWords {
    address internal constant KEVM_CHEATS = address(uint160(uint256(keccak256("hevm cheat code"))));

    KEVMCheatsBase internal constant kevm = KEVMCheatsBase(KEVM_CHEATS);

    function freshUInt256() external returns (uint256) {
        return kevm.freshUInt(32);
    }

    function freshUInt248() external returns (uint248) {
        return uint248(kevm.freshUInt(31));
    }

    function freshUInt240() external returns (uint240) {
        return uint240(kevm.freshUInt(30));
    }

    function freshUInt232() external returns (uint232) {
        return uint232(kevm.freshUInt(29));
    }

    function freshUInt224() external returns (uint224) {
        return uint224(kevm.freshUInt(28));
    }

    function freshUInt216() external returns (uint216) {
        return uint216(kevm.freshUInt(27));
    }

    function freshUInt208() external returns (uint208) {
        return uint208(kevm.freshUInt(26));
    }

    function freshUInt200() external returns (uint200) {
        return uint200(kevm.freshUInt(25));
    }

    function freshUInt192() external returns (uint192) {
        return uint192(kevm.freshUInt(24));
    }

    function freshUInt184() external returns (uint184) {
        return uint184(kevm.freshUInt(23));
    }

    function freshUInt176() external returns (uint176) {
        return uint176(kevm.freshUInt(22));
    }

    function freshUInt168() external returns (uint168) {
        return uint168(kevm.freshUInt(21));
    }

    function freshUInt160() external returns (uint160) {
        return uint160(kevm.freshUInt(20));
    }

    function freshUInt152() external returns (uint152) {
        return uint152(kevm.freshUInt(19));
    }

    function freshUInt144() external returns (uint144) {
        return uint144(kevm.freshUInt(18));
    }

    function freshUInt136() external returns (uint136) {
        return uint136(kevm.freshUInt(17));
    }

    function freshUInt128() external returns (uint128) {
        return uint128(kevm.freshUInt(16));
    }

    function freshUInt120() external returns (uint120) {
        return uint120(kevm.freshUInt(15));
    }

    function freshUInt112() external returns (uint112) {
        return uint112(kevm.freshUInt(14));
    }

    function freshUInt104() external returns (uint104) {
        return uint104(kevm.freshUInt(13));
    }

    function freshUInt96() external returns (uint96) {
        return uint96(kevm.freshUInt(12));
    }

    function freshUInt88() external returns (uint88) {
        return uint88(kevm.freshUInt(11));
    }

    function freshUInt80() external returns (uint80) {
        return uint80(kevm.freshUInt(10));
    }

    function freshUInt72() external returns (uint72) {
        return uint72(kevm.freshUInt(9));
    }

    function freshUInt64() external returns (uint64) {
        return uint64(kevm.freshUInt(8));
    }

    function freshUInt56() external returns (uint56) {
        return uint56(kevm.freshUInt(7));
    }

    function freshUInt48() external returns (uint48) {
        return uint48(kevm.freshUInt(6));
    }

    function freshUInt40() external returns (uint40) {
        return uint40(kevm.freshUInt(5));
    }

    function freshUInt32() external returns (uint32) {
        return uint32(kevm.freshUInt(4));
    }

    function freshUInt24() external returns (uint24) {
        return uint24(kevm.freshUInt(3));
    }

    function freshUInt16() external returns (uint16) {
        return uint16(kevm.freshUInt(2));
    }

    function freshUInt8() external returns (uint8) {
        return uint8(kevm.freshUInt(1));
    }

    function freshAddress() external returns (address) {
        return address(uint160(kevm.freshUInt(20)));
    }

    function freshSInt256() external returns (int256) {
        return int256(kevm.freshUInt(32));
    }

    function freshSInt248() external returns (int248) {
        return int248(uint248(kevm.freshUInt(31)));
    }

    function freshSInt240() external returns (int240) {
        return int240(uint240(kevm.freshUInt(30)));
    }

    function freshSInt232() external returns (int232) {
        return int232(uint232(kevm.freshUInt(29)));
    }

    function freshSInt224() external returns (int224) {
        return int224(uint224(kevm.freshUInt(28)));
    }

    function freshSInt216() external returns (int216) {
        return int216(uint216(kevm.freshUInt(27)));
    }

    function freshSInt208() external returns (int208) {
        return int208(uint208(kevm.freshUInt(26)));
    }

    function freshSInt200() external returns (int200) {
        return int200(uint200(kevm.freshUInt(25)));
    }

    function freshSInt192() external returns (int192) {
        return int192(uint192(kevm.freshUInt(24)));
    }

    function freshSInt184() external returns (int184) {
        return int184(uint184(kevm.freshUInt(23)));
    }

    function freshSInt176() external returns (int176) {
        return int176(uint176(kevm.freshUInt(22)));
    }

    function freshSInt168() external returns (int168) {
        return int168(uint168(kevm.freshUInt(21)));
    }

    function freshSInt160() external returns (int160) {
        return int160(uint160(kevm.freshUInt(20)));
    }

    function freshSInt152() external returns (int152) {
        return int152(uint152(kevm.freshUInt(19)));
    }

    function freshSInt144() external returns (int144) {
        return int144(uint144(kevm.freshUInt(18)));
    }

    function freshSInt136() external returns (int136) {
        return int136(uint136(kevm.freshUInt(17)));
    }

    function freshSInt128() external returns (int128) {
        return int128(uint128(kevm.freshUInt(16)));
    }

    function freshSInt120() external returns (int120) {
        return int120(uint120(kevm.freshUInt(15)));
    }

    function freshSInt112() external returns (int112) {
        return int112(uint112(kevm.freshUInt(14)));
    }

    function freshSInt104() external returns (int104) {
        return int104(uint104(kevm.freshUInt(13)));
    }

    function freshSInt96() external returns (int96) {
        return int96(uint96(kevm.freshUInt(12)));
    }

    function freshSInt88() external returns (int88) {
        return int88(uint88(kevm.freshUInt(11)));
    }

    function freshSInt80() external returns (int80) {
        return int80(uint80(kevm.freshUInt(10)));
    }

    function freshSInt72() external returns (int72) {
        return int72(uint72(kevm.freshUInt(9)));
    }

    function freshSInt64() external returns (int64) {
        return int64(uint64(kevm.freshUInt(8)));
    }

    function freshSInt56() external returns (int56) {
        return int56(uint56(kevm.freshUInt(7)));
    }

    function freshSInt48() external returns (int48) {
        return int48(uint48(kevm.freshUInt(6)));
    }

    function freshSInt40() external returns (int40) {
        return int40(uint40(kevm.freshUInt(5)));
    }

    function freshSInt32() external returns (int32) {
        return int32(uint32(kevm.freshUInt(4)));
    }

    function freshSInt24() external returns (int24) {
        return int24(uint24(kevm.freshUInt(3)));
    }

    function freshSInt16() external returns (int16) {
        return int16(uint16(kevm.freshUInt(2)));
    }

    function freshSInt8() external returns (int8) {
        return int8(uint8((kevm.freshUInt(1))));
    }
}

abstract contract KEVMUtils {
    // @notice Checks if an address matches one of the built-in addresses.
    function notBuiltinAddress(address addr) internal pure returns (bool) {
        return (addr != address(645326474426547203313410069153905908525362434349) &&
                addr != address(728815563385977040452943777879061427756277306518));
    }
}

abstract contract KEVMBase {
    address internal constant KEVM_CHEATS = address(uint160(uint256(keccak256("hevm cheat code"))));

    KEVMCheatsBase internal constant kevm = KEVMCheatsBase(KEVM_CHEATS);
}

abstract contract KEVMCheats is KEVMBase, KEVMUtils {}
