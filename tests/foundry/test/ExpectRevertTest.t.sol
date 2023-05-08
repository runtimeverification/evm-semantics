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

contract DepthReverter {
    Reverter reverter;

    constructor() {
        reverter = new Reverter();
    }

    function revertAtNextDepth() public view {
        reverter.revertWithoutReason();
    }
}

contract ReverterWithReturn {
    function returnBytesUnless(bool revertInstead)
        public
        returns (bytes memory)
    {
        if (revertInstead) {
            revert("Error");
        } else {
            return abi.encodePacked(bytes4(0xdeadbeef));
        }
    }

    function returnTupleUnless(bool revertInstead)
        public
        returns (uint256, uint256)
    {
        if (revertInstead) {
            revert("Error");
        } else {
            return (1, 2);
        }
    }
}

contract ExpectRevertTest is Test {
    error NotAuthorised(address caller, string message);

    function doRevert() internal pure {
        require(false, "");
    }

    function test_expectRevert_internalCall() public {
        vm.expectRevert();
        doRevert();
    }

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

    function testFail_expectRevert_empty() public {
        vm.expectRevert();
    }

    function testFail_expectRevert_multipleReverts() public {
        Reverter reverter = new Reverter();
        vm.expectRevert();
        reverter.revertWithoutReason();
        reverter.revertWithoutReason();
    }

    function test_ExpectRevert_increasedDepth() public {
        DepthReverter reverter = new DepthReverter();
        vm.expectRevert();
        reverter.revertAtNextDepth();
    }

    function testFail_ExpectRevert_failAndSuccess() public {
         Reverter reverter = new Reverter();
         vm.expectRevert();
         reverter.noRevert();
         vm.expectRevert();
         reverter.revertWithoutReason();
    }

    function test_expectRevert_encodedSymbolic(address controller) public {
        vm.startPrank(controller);
        vm.expectRevert(
            abi.encodeWithSelector(
                NotAuthorised.selector,
                controller,
                "TRANSFEROWNERSHIP"
            )
        );
        revert NotAuthorised(controller, "TRANSFEROWNERSHIP");
    }

    function test_expectRevert_returnValue() public {
        ReverterWithReturn reverter = new ReverterWithReturn();

        vm.expectRevert("Error");
        bytes memory returnValueBytes = reverter.returnBytesUnless(true);
        assertEq0(returnValueBytes, "");

        vm.expectRevert("Error");
        (uint256 fst, uint256 snd) = reverter.returnTupleUnless(true);
        assertEq(fst, 0);
        assertEq(snd, 0);
    }
}
