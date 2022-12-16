// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssumeTest is Test {

    function test_assume_true(uint256 a, uint256 b) public {
        vm.assume(a == b);
        assertEq(a, b);
    }

    function test_assume_false(uint256 a, uint256 b) public {
        vm.assume(a != b);
        assertEq(a, b);
    }

    function testFail_assume_true(uint256 a, uint256 b) public {
        vm.assume(a != b);
        assertEq(a, b);
    }

    function testFail_assume_false(uint256 a, uint256 b) public {
        vm.assume(a == b);
        assertEq(a, b);
    }

    function test_assume_staticCall(bool a) public {
        address addr = address(vm);
        assembly {
            let status := staticcall(16000, addr, add(a, 32), mload(a), 0, 0)
        }
        assertTrue(a);
    }
}