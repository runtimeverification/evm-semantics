pragma solidity =0.8.13;

import "forge-std/Test.sol";

import "../src/KEVMCheats.sol";

contract FreshVar is KEVMCheats {
    function freshUInt256() public returns (uint256) {
        bytes32 word = kevm.freshWord();
        return uint256(word);
    }

    function freshUInt128() public returns (uint128) {
        bytes32 word = kevm.freshWord();
        return uint128(uint256(word));
    }

    function freshAddress() public returns (address) {
        bytes32 word = kevm.freshWord();
        return address(uint160(uint256(word)));
    }
}

contract FreshWordTest is Test {
    FreshVar fv;

    function setUp() public {
        fv = new FreshVar();
    }

    function test_fresh_types() public {
        uint256 fresh_uint256 = fv.freshUInt256();
        assertGe(fresh_uint256, 0);
        assertLe(fresh_uint256, type(uint256).max);
        uint128 fresh_uint128 = fv.freshUInt128();
        assertGe(uint256(fresh_uint128), 0);
        assertLe(uint256(fresh_uint128), type(uint128).max);
        address fresh_address = fv.freshAddress();
        assertGe(uint256(uint160(fresh_address)), 0);
        assertLe(uint256(uint160(fresh_address)), type(uint160).max);
    }
}
