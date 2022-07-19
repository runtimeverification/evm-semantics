pragma solidity 0.8.10;

import "forge-std/Test.sol";

contract BlockParamsTest is Test {

    function testWarp(uint256 time) public {
        vm.warp(time);
        assertEq(block.timestamp, time);
    }

    function testRoll(uint256 newHeight) public {
        vm.roll(newHeight);
        assertEq(block.number, newHeight);
    }

    function testFee(uint256 newFee) public {
        vm.fee(newFee);
        assertEq(block.basefee, newFee);
    }

    function testChainId(uint256 newChainId) public {
        vm.chainId(newChainId);
        assertEq(block.chainid, newChainId);
    }

}