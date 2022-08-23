// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract AssertTest {
    function setUp() public {}

    function test_assert_true() public pure {
        assert(true);
    }

    function test_assert_false() public pure {
        assert(false);
    }

    function testFail_assert_true() public pure {
        assert(true);
    }

    function testFail_assert_false() public pure {
        assert(false);
    }
}
