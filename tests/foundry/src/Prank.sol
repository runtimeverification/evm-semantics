// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

error Unauthorized();

contract Prank {
    address public immutable owner;
    uint256 public count;

    constructor() {
        owner = msg.sender;
    }

    function add(uint256 value) external {
        require(msg.sender == owner, "Only owner");
        count += value;
    }

    function subtract(uint256 value) external {
        require(tx.origin == address(0));
        require(count >= value);
        count -= value;
    }
}