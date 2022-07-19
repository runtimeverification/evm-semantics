pragma solidity 0.8.10;

import "forge-std/Test.sol";

error Unauthorized();

contract OwnerUpOnly {
    address public immutable owner;
    uint256 public count;

    constructor() {
        owner = msg.sender;
    }

    function increment() external {
        if (msg.sender != owner) {
            revert Unauthorized();
        }
        count++;
    }
}

contract OwnerUpOnlyTest is Test {
    OwnerUpOnly upOnly;

    //function setUp() public {
    //    upOnly = new OwnerUpOnly();
    //}

    function testIncrementAsOwner() public {
        upOnly = new OwnerUpOnly();
        assertEq(upOnly.count(), 0);
        upOnly.increment();
        assertEq(upOnly.count(), 1);
    }

    function testFailIncrementAsNotOwner() public {
        upOnly = new OwnerUpOnly();
        vm.prank(address(0));
        upOnly.increment();
    }
}
