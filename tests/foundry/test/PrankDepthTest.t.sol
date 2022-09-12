// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Test.sol";

contract PrankDepth1 {
    address constant alice = address(47153);
    address public immutable owner;
    PrankDepth2 public depth2;

    constructor() {
        owner = msg.sender;
    }

    function noOwnerYesAlice() public {
        assert(msg.sender != owner);
        assert(msg.sender == alice);
        depth2 = new PrankDepth2();
        depth2.noAlice();
    }
}

contract PrankDepth2 {
    address constant alice = address(47153);

    function noAlice() public view {
        assert(msg.sender != alice);
    }
}

contract PrankDepthTest is Test {
    address constant alice = address(47153);
    PrankDepth1 public depth1;

    function testPrankDepth() public {
        depth1 = new PrankDepth1();
        vm.startPrank(address(alice));
        depth1.noOwnerYesAlice();
        vm.stopPrank();
    }
}
