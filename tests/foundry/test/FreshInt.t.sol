pragma solidity =0.8.13;

import "forge-std/Test.sol";

import "../src/KEVMCheats.sol";

contract FreshIntTest is Test, KEVMCheats {
    function test_uint256() public {
        uint256 fresh_uint256 = kevm.freshUInt(32);
        assertGe(fresh_uint256, type(uint256).min);
        assertLe(fresh_uint256, type(uint256).max);
    }

    function test_uint128() public {
        uint256 fresh_uint128 = kevm.freshUInt(16);
        assertGe(fresh_uint128, type(uint128).min);
        assertLe(fresh_uint128, type(uint128).max);
    }

    function test_int256() public {
        int256 fresh_int256 = kevm.freshSInt(16);
        assertGe(fresh_int256, type(int256).min);
        assertLe(fresh_int256, type(int256).max);
    }

    function test_int128() public {
        int256 fresh_int128 = kevm.freshSInt(8);
        assertGe(fresh_int128, type(int128).min);
        assertLe(fresh_int128, type(int128).max);
    }

    function test_bool() public {
        kevm.infiniteGas();
        bool fresh_bool = kevm.freshBool();
        uint256 as_int;
        assembly {
            as_int := fresh_bool
        }
        assertLe(as_int, 1);
    }
}
