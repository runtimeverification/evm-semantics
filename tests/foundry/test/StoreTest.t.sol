// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Test.sol";

contract Store {
    uint256 private testNumber = 1337; // slot 0

    constructor(){
    }
}

contract StoreTest is Test {

    Store myStore;

    function setUp() public {
        vm.record();
        myStore = new Store();
    }

    function testAccesses() public {
        (bytes32[] memory reads, bytes32[] memory writes) = vm.accesses(address(myStore));
        assertEq(reads.length, 1);
        assertEq(writes.length, 1);
    }

    function testStoreLoad() public {
        vm.store(address(myStore), bytes32(uint256(0)), bytes32(uint256(31337)));
        bytes32 testNumber = vm.load(address(myStore), bytes32(uint256(0)));
        assertEq(uint256(testNumber), 31337); // 31337
    }
}
