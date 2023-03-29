// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract SymbolicStore {
    uint256 private testNumber = 1337; // slot 0
    constructor() {}
}

contract SymbolicStorageTest is Test, KEVMCheats { 
    function testFail_SymbolicStorage(uint256 slot) public {
         address addr = 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8;
         kevm.symbolicStorage(addr);
         bytes32 value = vm.load(addr, bytes32(slot));
         require(value != 0);
         assertEq(uint256(value), 0);
    }

    function testFail_SymbolicStorage1(uint256 slot) public {
        SymbolicStore myStore = new SymbolicStore();
        kevm.symbolicStorage(address(myStore));
        bytes32 value = vm.load(address(myStore), bytes32(uint256(slot)));
        require(value != 0);
        assertEq(uint256(value), 0);
    }

    function testEmptyInitialStorage(uint256 slot) public {
        bytes32 storage_value = vm.load(address(vm), bytes32(slot));
        assertEq(uint256(storage_value), 0);
    }
}
