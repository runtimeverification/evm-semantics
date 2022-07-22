// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Test.sol";
import "src/Prank.sol";

contract PrankTest is Test {
    Prank prankContract;

    function setUp() public {
        prankContract = new Prank();
    }

    function testAddAsOwner(uint256 x) public {
        assertEq(prankContract.count(), 0);
        prankContract.add(x);
        assertEq(prankContract.count(), x);
    }

    function testFailAddPrank(uint256 x) public {
        vm.prank(address(0));
        prankContract.add(x);
    }

    function testAddStartPrank(uint256 x) public {
        vm.expectRevert(Unauthorized.selector);
        vm.startPrank(address(0));
        prankContract.add(x);
        assertEq(prankContract.count(), 0);
    }

    function testAddStopPrank(uint256 x) public {
        vm.stopPrank();
        assertEq(prankContract.count(), 0);
        prankContract.add(x);
        assertEq(prankContract.count(), x);
    }

    function testSubtractAsTxOrigin(uint256 addValue, uint256 subValue) public {
        prankContract.add(addValue);
        vm.assume(subValue<=addValue);
        vm.prank(address(0), address(0));
        prankContract.subtract(subValue);
        assertEq(prankContract.count(), addValue-subValue);
    }

    function testSubtractStartPrank(uint256 addValue, uint256 subValue) public {
        prankContract.add(addValue);
        vm.startPrank(address(0),address(0));
        vm.assume(subValue<=addValue);
        prankContract.subtract(subValue);
        assertEq(prankContract.count(), addValue-subValue);
        vm.stopPrank();
    }
}
