// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract AssertTest is Test {
    uint y;

    function setUp() public {}

    function test_failing_branch(uint x) public {
      assert(x >= 100);
    }

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

    struct Pack {
        uint8 x;
        uint64 y;
    }

    function test_call(Pack calldata pack) public {
        vm.assume(pack.x > 10);
        address(2819807389471923).call(abi.encodeWithSignature("func(uint256)", pack.x));
    }

    function test_prank() public {
        vm.prank(address(7482741294), address(123456789));
        address(2819807389471923).call(abi.encodeWithSignature("func()"));
    }

    function test_not_null_sig(bytes4 sig) public {
        vm.assume(sig != 0x00000000);
        address(726378162386128763879123).call(abi.encode(sig));
    }

    function test_simple(uint256 x) public {
        vm.assume(!(x > 10));
        vm.assume(x < 5);
        address(7478948923748124).call(abi.encodeWithSignature("func(uint256)", x));
    }

    function test_bool(bool x) public {
        vm.assume(!x == true);
        address(7686812637812839).call(abi.encodeWithSignature("func(bool)", x));
    }
}
