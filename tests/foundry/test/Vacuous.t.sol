// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract VacuousTest is Test {
    function atLeastOneIsValidAddress(address alice, address bob)
        internal
        returns (bool)
    {
        if (alice != address(0)) {
            return true;
        } else if (bob != address(0)) {
            return true;
        } else {
            return false;
        }
    }

    function test_assume_return(address alice, address bob) public {
        vm.assume(atLeastOneIsValidAddress(alice, bob));

        assert(true);
    }

    function test_far_between(bool flag) public {
        vm.assume(flag);
        assert(true);
        vm.assume(!flag);
        assert(false);
    }

    function test_unreachable(bool flag) public {
        vm.assume(false);
        assert(false);
    }
}
