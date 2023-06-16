// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

contract AmbiguousTest {
    function test_assert_true() public pure {
        assert(true);
    }

    function test_assert_true(uint256) public pure {
        assert(true);
    }

    function test_assert_true(uint8) public pure {
        assert(true);
    }

    function test_array_type(uint256) public {
        assert(true);
    }

    function test_array_type(uint256[] calldata numbers) public {
        assert(true);
    }
}
