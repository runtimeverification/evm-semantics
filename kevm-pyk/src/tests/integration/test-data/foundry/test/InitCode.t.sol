// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract InitCodeTest is Test {

    uint a = 4;
    uint b = 100;
    uint c = 100;

    constructor() public payable {
        b = 2;
        c = 200;
    }

    function setUp() public {
        c = 1;
    }

    function test_init() public {
        assertEq(a + b + c, 7);
    }
    function testFail_init() public {
        assertEq(a + b + c, 8);
    }
}
