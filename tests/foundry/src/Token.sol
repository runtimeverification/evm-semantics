// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract Token {
    uint256 x;
    mapping(address => uint256) balances;
    mapping(address => mapping(address => uint256)) allowances;
}
