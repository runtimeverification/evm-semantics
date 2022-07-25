// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

contract TestNumber {
    uint256 public testNumber ;

    constructor(uint256 initial){
        testNumber = initial;
    }

    function setNumber(uint256 number) public {
        testNumber = number;
    }

}