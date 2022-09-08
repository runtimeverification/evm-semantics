// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract Depth2 {

    function secondDepth() public view {
        assert(true);
    }
}

contract Depth1 {

    Depth2 public depth2;

    function firstDepth() public {
        assert(true);
        depth2 = new Depth2();
        depth2.secondDepth();
    }
}

contract DepthTest {

    Depth1 public depth1;

    function testDepth() public {
        depth1 = new Depth1();
        depth1.firstDepth();
    }
}
