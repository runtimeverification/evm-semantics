// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract NonceTest is Test {

    //function setUp() public{}

    function testNonce(uint64 newNonce) public {
       uint64 oldnonce = vm.getNonce(address(this));
       vm.assume(newNonce > oldnonce);
       vm.setNonce(address(this), newNonce);
       assertEq(vm.getNonce(address(this)),newNonce);
    }

    function test_GetNonce_true() public {
       uint64 nonce = vm.getNonce(address(this));
       assert(nonce == 1);
    }

    function test_GetNonce_false() public {
       uint64 nonce = vm.getNonce(address(100));
       assertEq(nonce, 10);
    }

    function testFail_GetNonce_true() public {
       uint64 nonce = vm.getNonce(address(0));
       assertEq(nonce, 10);
    }

    function testFail_GetNonce_false() public {
       uint64 nonce = vm.getNonce(address(this));
       assertGt(nonce, 0);
    }
    /*function test_SetNonce() public {   Passes
       uint64 nonce = vm.getNonce(address(this));
       assert(nonce == 0);
    }

    function test_SetNonce() public { //Fails
       vm.setNonce(address(100), 100);
       uint64 nonce = vm.getNonce(address(100));
       assert(nonce == 100);
    }

    function test_SetNonce() public { //Fails
       uint64 nonce = vm.getNonce(address(100));
       assert(nonce == 100);
    }

    function test_SetNonce() public { //fails
       uint64 nonce = vm.getNonce(address(this));
       assert(nonce == 100);
    }

    function test_SetNonce() public { //fails
       uint64 nonce = vm.getNonce(address(this));
       assert(nonce == 1);
    }

    function test_SetNonce() public { //passes
       uint64 nonce = vm.getNonce(address(this));
       assertEq(nonce, 1);
    }

    function test_SetNonce() public { //passes
       uint64 nonce = vm.getNonce(address(this));
       assertEq(nonce, 0);
    }

    function test_SetNonce() public { // it should pass and now passes on KEVM
       uint64 nonce = vm.getNonce(address(this));
       assert(nonce == 1);
    }

    function test_SetNonce() public { //it should fail and now fails on KEVM
       uint64 nonce = vm.getNonce(address(this));
       assert(nonce == 0);
    }

    function test_SetNonce() public { //it should pass and now passes
       uint64 nonce = vm.getNonce(address(100));
       assert(nonce == 0);
    }
    */

    function test_SetNonce_this() public {
       vm.setNonce(address(this), 100);
       uint64 nonce = vm.getNonce(address(this));
       assert(nonce == 100);
    }

    function test_SetNonce_100() public {
       vm.setNonce(address(100), 100);
       uint64 nonce = vm.getNonce(address(100));
       assert(nonce == 100);
    }

}
