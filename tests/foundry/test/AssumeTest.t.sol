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
        address(vm).staticcall(abi.encodeWithSignature("assume(bool)", a));
        assert(a);
    }

    function test_multi_assume(address alice, address bob) public {
        vm.assume(alice != address(120209876281281145568259943));
        vm.assume(alice != address(137122462167341575662000267002353578582749290296));
        vm.assume(alice != address(645326474426547203313410069153905908525362434349));
        vm.assume(alice != address(728815563385977040452943777879061427756277306518));

        vm.assume(bob != address(120209876281281145568259943));
        vm.assume(bob != address(137122462167341575662000267002353578582749290296));
        vm.assume(bob != address(645326474426547203313410069153905908525362434349));
        vm.assume(bob != address(728815563385977040452943777879061427756277306518));
    }
}
