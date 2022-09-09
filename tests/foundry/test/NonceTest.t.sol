// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract NonceTest is Test {

    function setUp() public{}

    function testNonce(uint64 newNonce) public {
       uint64 oldnonce = vm.getNonce(address(this));
       vm.assume(newNonce > oldnonce);
       vm.setNonce(address(this), newNonce);
       assertEq(vm.getNonce(address(this)),newNonce);
    }

    function test_GetNonce_true() public {
       uint64 nonce = vm.getNonce(address(this));
       assertGt(nonce,0);
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

/*
    function test_SetNonce() public {
       uint64 oldnonce = vm.getNonce(address(this));
       vm.setNonce(address(this), oldnonce+1);
       assertEq(vm.getNonce(address(this)),oldnonce+1);
    }
    */

    function test_SetNonce() public {
       vm.setNonce(address(100), 100);
       uint64 nonce = vm.getNonce(address(100));
       assert(nonce == 100);
    }

}
