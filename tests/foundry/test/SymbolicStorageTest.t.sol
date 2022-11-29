// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/Vm2.sol";

contract SymbolicStore {
    uint256 private testNumber = 1337; // slot 0

    constructor(){
    }
}

contract SymbolicStorageTest is Test { 
    address constant private VM_ADDRESS =
        address(bytes20(uint160(uint256(keccak256('hevm cheat code')))));
    Vm2 public constant vm2 = Vm2(VM_ADDRESS);

    function testFail_SymbolicStorage(uint256 slot) public {
         address addr = 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8;
         vm2.symbolicStorage(addr);
         bytes32 value = vm2.load(addr, bytes32(slot));
         require(value != 0);
         assertEq(uint256(value), 0);
    }

    function testFail_SymbolicStorage1(uint256 slot) public {
        SymbolicStore myStore = new SymbolicStore();
        vm2.symbolicStorage(address(myStore));
        bytes32 value = vm2.load(address(myStore), bytes32(uint256(slot)));
        require(value != 0);
        assertEq(uint256(value), 0);
    }
}
