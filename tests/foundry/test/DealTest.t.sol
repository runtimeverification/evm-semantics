// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract DealToken{

}

contract DealTest is Test {

    function testDealConcrete() public {
        DealToken alice = new DealToken();
        vm.deal(address(alice), 256);
        assertEq(address(alice).balance, 256);
    }

    function testDealSymbolic(uint256 value) public {
        DealToken alice = new DealToken();
        vm.deal(address(alice), value);
        assertEq(address(alice).balance, value);
    }

    function testDealNonExistingAccount() public {
        vm.deal(address(0), 1 ether);
        assert(address(0).balance == 1 ether);
    }
}
