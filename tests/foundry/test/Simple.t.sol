// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssertTest is Test {
    uint y;

    function test_assert_true() public pure {
        assert(true);
    }

    function test_assert_true_branch(uint x) public {
        if (x < 3) {
            y = x;
            assert(true);
        } else {
            y = x - 1;
            assert(true);
        }
        assert(y <= x);
    }

    function test_assert_false() public pure {
        assert(false);
    }

    function testFail_assert_true() public pure {
        assert(true);
    }

    function testFail_assert_false() public pure {
         assert(false);
     }

    function testFail_expect_revert() public {
        vm.expectRevert();
        assert(false);
    }

    function test_revert_branch(uint x, uint y) public{
        if (x < y) {
            assert(true);
        } else {
            assert(false);
        }
    }

<<<<<<< HEAD
    function test_call() public {
        address(123456).call("");
        assert(true);
=======
    function test_call(uint256 val) public {
        // address(123456).call{gas: 99999}("not_a_selector()");
        // address who = address(uint160(uint256(bytes32(keccak256("who")))));
        address to = address(uint160(uint256(bytes32(keccak256("to")))));
        // who.call{value: 1 ether}(abi.encodeWithSignature("transfer(address,uint256)", to, 500));
        to.call(abi.encode(val));
    }

    function test_delegate() public {
        address(this).delegatecall(abi.encodeWithSignature("transfer(address,uint256)", address(10987654321), 500));
    }

    function test_simple_call() public {
        address(123456).call("");
>>>>>>> 20ed57bb66751a2eb6014054afba3c476132a6f6
    }
}
