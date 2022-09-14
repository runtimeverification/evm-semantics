// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

contract UintTypeTest {
    function setUp() public {}

    function test_uint256(uint256 x) public pure {
        assert(x == x);
        assert(type(uint256).max >= x);
    }

    function testFail_uint256(uint256 x) public pure {
        assert(type(uint256).max > x);
    }

    function test_uint224(uint224 x) public pure {
        assert(x == x);
        assert(type(uint224).max >= x);
    }

    function testFail_uint224(uint224 x) public pure {
        assert(type(uint224).max > x);
    }

    function test_uint160(uint160 x) public pure {
        assert(x == x);
        assert(type(uint160).max >= x);
    }

    function testFail_uint160(uint160 x) public pure {
        assert(type(uint160).max > x);
    }

    function test_uint144(uint144 x) public pure {
        assert(x == x);
        assert(type(uint144).max >= x);
    }

    function testFail_uint144(uint144 x) public pure {
        assert(type(uint144).max > x);
    }

    function test_uint112(uint112 x) public pure {
        assert(x == x);
        assert(type(uint112).max >= x);
    }

    function testFail_uint112(uint112 x) public pure {
        assert(type(uint112).max > x);
    }

}
