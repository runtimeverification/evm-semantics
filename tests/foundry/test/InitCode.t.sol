// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract InitCodeTest is Test {

    uint a = 1;
    uint b = 2;
    uint c = 3;

    constructor() public payable {
    }

    function test_init() public {
        assertEq(a + b + c, 6);
    }
    function testFail_init() public {
        assertEq(a + b + c, 7);
    }
}
