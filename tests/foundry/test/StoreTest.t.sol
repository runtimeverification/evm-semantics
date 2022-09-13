// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract Store {
    uint256 private testNumber = 1337; // slot 0

    constructor(){
    }
}

contract StoreTest is Test {

    function testAccesses() public {
        Store myStore = new Store();
        vm.record();

        (bytes32[] memory reads, bytes32[] memory writes) = vm.accesses(address(myStore));
        assertEq(reads.length, 1);
        assertEq(writes.length, 1);
    }

    function testStoreLoad() public {
        Store myStore = new Store();
        vm.store(address(myStore), bytes32(uint256(0)), bytes32(uint256(31337)));
        bytes32 testNumber = vm.load(address(myStore), bytes32(uint256(0)));
        assertEq(uint256(testNumber), 31337); // 31337
    }

    function testStoreLoadNonExistent() public {
        vm.store(address(0), bytes32(uint256(3)), bytes32(uint256(31337)));
        bytes32 testNumber = vm.load(address(0), bytes32(uint256(3)));
        assertEq(uint256(testNumber), 31337); // 31337
    }

    function testLoadNonExistent() public {
        bytes32 testNumber = vm.load(address(100), bytes32(uint256(23)));
        assertEq(uint256(testNumber), 0);
    }
}
