pragma solidity 0.8.10;

import "forge-std/Test.sol";

contract WarpTest is Test {

    function testWarp(uint256 time) public {
        vm.warp(time);
        assertEq(block.timestamp, time);
    }

}