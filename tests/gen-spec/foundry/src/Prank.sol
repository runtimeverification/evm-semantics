// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

error Unauthorized();

contract Prank {
    address public immutable owner;
    uint256 public count;

    constructor() {
        owner = msg.sender;
    }

    function add(uint256 value) external {
        if (msg.sender != owner) {
            revert Unauthorized();
        }
        count += value;
    }

    function subtract(uint256 value) external {
        if (tx.origin != address(0)) {
            revert Unauthorized();
        }
        require(count >= value);
        count -= value;
    }
}