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
        require(msg.sender != owner);
        count = count + 1;
    }
}

contract PlainPrankTest is Test {

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

}