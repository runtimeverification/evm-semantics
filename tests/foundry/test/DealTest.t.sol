// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract Token{

}

contract DealTest is Test {

    function testDealConcrete() public {
        Token alice = new Token();
        vm.deal(address(alice), 256);
        assertEq(address(alice).balance, 256);
    }

    function testDealSymbolic(uint256 value) public {
        Token alice = new Token();
        vm.deal(address(alice), value);
        assertEq(address(alice).balance, value);
    }
}