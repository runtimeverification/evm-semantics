// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "src/Prank.sol";
import "forge-std/Test.sol";

contract BroadcastTest is Test {
    Prank test;

    function setUp() public {
        test = new Prank();
    }
    
    function testBroadcast() public {
        vm.broadcast();
        // this won't generate tx to sign
        vm.expectRevert(bytes("Only owner"));
        test.add(10);
        assertEq(test.count(),0);
    } 

    function testBroadcastaddress() public {
        // this will
        vm.broadcast(address(0));
        test.subtract(5);
        assertEq(test.count(),5);
    }
}
