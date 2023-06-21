pragma solidity =0.8.13;

import "forge-std/Test.sol";

import "../src/KEVMCheats.sol";

contract FreshIntTest is Test, KEVMCheats {
    function test_uint256() public {
        kevm.infiniteGas();
        uint256 fresh_uint256 = uint256(kevm.freshUInt(32));
        assertGe(fresh_uint256, type(uint256).min);
        assertLe(fresh_uint256, type(uint256).max);
    }

    // function test_uint128() public {
    //     kevm.infiniteGas();
    //     uint256 fresh_uint128 = kevm.freshUInt(16);
    //     assertGe(fresh_uint128, type(uint128).min);
    //     assertLe(fresh_uint128, type(uint128).max);
    // }

    function test_int128() public {
        kevm.infiniteGas();
        uint256 fresh_uint128 = kevm.freshUInt(16);
        assertLe(fresh_uint128, type(uint128).max);
        int128 fresh_int128 = int128(uint128(uint256(fresh_uint128)));
        assertGe(fresh_int128, type(int128).min);
        assertLe(fresh_int128, type(int128).max);
    }

    function test_bool() public {
        kevm.infiniteGas();
        uint256 fresh_uint256 = kevm.freshBool();
        assertGe(fresh_uint256, 0);
        assertLe(fresh_uint256, 1);
    }

    function test_int() public {
        kevm.infiniteGas();
        // int128 s;
        // uint256 u = uint256(kevm.freshUInt(16));
        int128 s = int128(uint128(uint256(kevm.freshUInt(16))));
        // assembly {
        //     s := u
        // }
        assertGe(s, type(int128).min);
        assertLe(s, type(int128).max);
    }
}
