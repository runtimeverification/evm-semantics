// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

// This experiment covers the basic behavior of the
// test contract constructor and setup function.
//
// In particular, it ensures that the constructor
// and setup functions are called before running
// the tests.
//
// The setup function is called exactly once after
// the constructor function.
//
// Before each test the VM reverts to the post
// setup state.
contract SetUpTest is Test {
    
    uint256 counter = 0;

    constructor () {
        counter = 100;
    }

    function setUp() public{
        counter++;
    }

    function testSetUpCalled() public {
        assertEq(counter, 101);
    }

    // We also want to cover a symbolic case
    function testSetUpCalledSymbolic(uint256 x) public {
        assertEq(counter, 101);
        // The following assertion is only here so that
        // x is used and not thrown away by the optimizer
        assertEq(x, x);
    }
}
