// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract AssumeSetUpTest is Test, KEVMCheats {
    uint256 n;

    function setUp() public {
        kevm.symbolicStorage(address(this));
        vm.assume(n < 10);
    }

    function testAssumeSetUp() public {
        assertLt(n, 10);
    }
}
