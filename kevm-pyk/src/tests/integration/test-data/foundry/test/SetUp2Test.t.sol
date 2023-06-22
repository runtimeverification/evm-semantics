// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract Setup2Test is Test {

    uint a;
    uint b;
    uint c;

    function setUp() public {
        a = 1;
        b = 2;
        c = 3;
    }

    function test_setup() public {
        assertEq(a + b + c, 6);
    }
    function testFail_setup() public {
        assertEq(a + b + c, 7);
    }
}
