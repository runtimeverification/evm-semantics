// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "src/MyToken.sol";

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
contract SetUpDeployTest is Test {

    MyToken token;

    function setUp() public{
        token = new MyToken(address(0));
    }

    function test_extcodesize() public {
        uint size;
        address token_addr = address(token);
        assembly {
            size := extcodesize(token_addr)
        }
        assert(size > 0);
    }
}
