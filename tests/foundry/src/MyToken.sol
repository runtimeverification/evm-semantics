// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

contract MyToken{
    address public token;
    mapping (address => uint256) public balances;

    constructor(address sometoken) {
        token = sometoken;
    }

    function balanceOf(address user) external view returns (uint256) {
        return balances[user];
    }

    receive() external payable {}

    function pay(address user) external payable returns (uint256) {
        balances[user]+=msg.value;
        return balances[user];
    }
}
