// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract LabelTest is Test {

    function testLabel() public {
        address addrA = 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8;
        vm.label(addrA,"Alice");
        //Just to check test trace
        assertEq(addrA,0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8);
    }
}