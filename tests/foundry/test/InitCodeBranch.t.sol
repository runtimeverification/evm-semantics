// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract InitCodeBranchTest is Test, KEVMCheats {

    uint b;

    constructor(uint a) public payable {
        if(a <= 10) {
            b = 1;
        }
        else {
            b = 2;
        }
    }

    function test_branch() public {
        assertEq(b, 1);
    }
}
