// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract Reverter {
    function revertWithoutReason() public pure {
        revert();
    }

    function revertWithReason(string calldata _a) public pure {
        revert(_a);
    }

    function noRevert() public pure returns (bool) {
        return true;
    }
}

contract ExpectRevertTest is Test {
    function test_expectRevert_true() public {
        Reverter reverter = new Reverter();
        vm.expectRevert();
        reverter.revertWithoutReason();
    }

    function testFail_expectRevert_false() public {
        Reverter reverter = new Reverter();
        vm.expectRevert();
        reverter.noRevert();
    }

    function test_expectRevert_message() public {
        Reverter reverter = new Reverter();
        vm.expectRevert(bytes("Revert Reason Here"));
        reverter.revertWithReason("Revert Reason Here");
    }

    function testFail_expectRevert_bytes4() public {
        Reverter reverter = new Reverter();
        vm.expectRevert(bytes4("FAIL"));
        reverter.revertWithReason("But fail.");
    }

    function test_expectRevert_bytes4() public {
        Reverter reverter = new Reverter();
        vm.expectRevert(bytes4("FAIL"));
        reverter.revertWithReason("FAIL");
    }
}