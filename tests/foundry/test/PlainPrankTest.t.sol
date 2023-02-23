// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AdditionalToken {
    address public immutable owner;
    uint256 public count;

    constructor() {
        owner = msg.sender;
        count = 0;
    }

    function incrementCount() public {
        if(msg.sender != owner)
            count = count + 1;
    }
}

contract PlainPrankTest is Test {

    function internalCounter() public view returns (bool) {
        return msg.sender == address(15);
    }

    function testFail_startPrank_internalCall() public {
        // The vm.assume is required only by KEVM in order to have this test passing. It is required
        // because the `msg.sender` in KEVM specs is a symbolic `CALLER_ID` while in foundry it is a
        // concrete, hardcoded address.
        vm.assume(msg.sender != address(15));
        vm.startPrank(address(15));
        assert(internalCounter());
    }

    function test_startPrank_true() public {
        AdditionalToken token = new AdditionalToken();
        vm.startPrank(address(token));
        token.incrementCount();
        vm.stopPrank();
        assert(token.count() == 1);
    }

    function test_startPrankWithOrigin_true() public {
        AdditionalToken token = new AdditionalToken();
        vm.startPrank(address(token), address(token));
        token.incrementCount();
        vm.stopPrank();
        assert(token.count() == 1);
    }

    function test_startPrank_zeroAddress_true() public {
        AdditionalToken token = new AdditionalToken();
        vm.startPrank(address(0));
        token.incrementCount();
        vm.stopPrank();
        assert(token.count() == 1);
    }

    function test_stopPrank_notExistent() public {
        vm.stopPrank();
        assert(true);
    }

    function testFail_startPrank_existingAlready() public {
        vm.startPrank(address(0));
        vm.startPrank(address(1));
        vm.stopPrank();
        vm.stopPrank();
    }

    function test_prank_zeroAddress_true() public {
        AdditionalToken token = new AdditionalToken();
        vm.prank(address(0));
        token.incrementCount();
        token.incrementCount();
        assert(token.count() == 1);
    }
}