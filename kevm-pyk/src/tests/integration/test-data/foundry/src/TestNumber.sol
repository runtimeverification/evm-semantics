// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "ds-test/test.sol";

contract TestNumber is DSTest{
    uint256 public testNumber ;

    constructor(uint256 initial){
        testNumber = initial;
    }

    function t(uint256 a) public returns (uint256) {
        uint256 b = 0;
        testNumber = a;
        emit log_string("here");
        return b;
    }

}