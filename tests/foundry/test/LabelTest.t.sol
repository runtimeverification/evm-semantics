// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract LabelTest is Test {

    function testLabel() public {
        vm.label(address(0), "Zero Address");
        //Just to check test trace
        assert(true);
    }
}