// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

contract NoImport {
    function test_source_map() public pure returns (uint) {
        uint x = 0;
        uint y = 1;
        uint z = 2;
        uint a = x + y;
        uint b = z - y;
        uint c = a * b;
        return a + b + c;
    }
}

