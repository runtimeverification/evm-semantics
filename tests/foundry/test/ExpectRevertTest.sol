// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract Reverter {
    function revertWithoutReason() public {
        revert();
    }

    function revertWithReason(string calldata _a) public {
        revert(_a);
    }

    function noRevert() public returns (bool) {
        return true;
    }
}
contract ExpectRevertTest is Test {

    function test_expectRevert_true() public {
        Reverter reverter = new Reverter();
        vm.expectRevert();
        reverter.revertWithoutReason();
    }

    function test_expectRevert_false() public {
        Reverter reverter = new Reverter();
        vm.expectRevert();
        reverter.noRevert();
    }
}