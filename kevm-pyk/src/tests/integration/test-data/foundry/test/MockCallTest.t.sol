// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "src/MyToken.sol";
import "src/MyIERC20.sol";


contract MockCallTest is Test {

    function testMockCall() public {
        vm.mockCall(
            address(0),
            abi.encodeWithSelector(MyToken.balanceOf.selector, address(1)),
            abi.encode(10)
        );
        assertEq(MyIERC20(address(0)).balanceOf(address(1)), 10);
    }

    function testMockCalls() public {
        vm.mockCall(
            address(0),
            abi.encodeWithSelector(MyToken.balanceOf.selector),
            abi.encode(10)
        );
        assertEq(MyIERC20(address(0)).balanceOf(address(1)), 10);
        assertEq(MyIERC20(address(0)).balanceOf(address(2)), 10);
        vm.clearMockedCalls();
    }

    function testMockCallValue() public {
        MyToken token = new MyToken(address(1337));

        assertEq(token.pay{value: 10}(address(1)), 10);
        assertEq(token.pay{value: 2}(address(2)), 2);
        vm.mockCall(
            address(token),
            10,
            abi.encodeWithSelector(MyToken.pay.selector),
            abi.encode(99)
        );
        assertEq(token.pay{value: 10}(address(1)), 99);
        assertEq(token.pay{value: 2}(address(2)), 4);
    }
}
