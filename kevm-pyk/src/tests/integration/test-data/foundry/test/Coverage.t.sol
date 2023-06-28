pragma solidity =0.8.13;

import "forge-std/Test.sol";

import "src/Coverage.sol";

contract CoverageTest is Test {
    Coverage cov;

    function setUp() public {
        cov = new Coverage();
    }

    function test_f_1(uint256 x) public {
        vm.assume(x < 10);
        uint256 y = cov.f(x);
        assertEq(y, 0);
    }

    function test_f_2(uint256 x) public {
        vm.assume(x >= 10);
        vm.assume(x < 20);
        uint256 y = cov.f(x);
        assertEq(y, 5);
    }

    function test_f_3() public {
        uint256 y = cov.f(238);
        assertGt(y, 0);
    }
}
