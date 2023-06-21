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
        assert(reads.length == 1);
        assert(writes.length == 1);
    }

    function testStoreLoad() public {
        Store myStore = new Store();
        vm.store(address(myStore), bytes32(uint256(0)), bytes32(uint256(31337)));
        bytes32 testNumber = vm.load(address(myStore), bytes32(uint256(0)));
        assert(uint256(testNumber) == 31337); // 31337
    }

    function testStoreLoadNonExistent() public {
        vm.store(address(0), bytes32(uint256(3)), bytes32(uint256(31337)));
        bytes32 testNumber = vm.load(address(0), bytes32(uint256(3)));
        assert(uint256(testNumber) == 31337); // 31337
    }

    function testLoadNonExistent() public {
        bytes32 testNumber = vm.load(address(100), bytes32(uint256(23)));
        assert(uint256(testNumber) == 0);
    }


    function testGasLoadColdVM() public {
        // Call vm.load(address(101), bytes32(uint256(23)))
        uint256 gasUsed = measureGasForCall(address(vm), abi.encodeCall(Vm.load, (address(101), bytes32(uint256(23)))));
        assert(gasUsed == 2625);
    }

    function testGasStoreColdVM() public {
        // Call vm.store(address(101), bytes32(uint256(23)), bytes32(uint256(5)))
        uint256 gasUsed = measureGasForCall(address(vm), abi.encodeCall(Vm.store, (address(101), bytes32(uint256(23)), bytes32(uint256(5)))));
        assert(gasUsed == 2625);
    }

    function testGasLoadWarmVM() public {
        // Load the vm into the set of accessed accounts. Should make the
        // following call to vm.load() cheaper
        (payable(address(vm)).send(0));

        // Call vm.load(address(101), bytes32(uint256(23)));
        uint256 gasUsed = measureGasForCall(address(vm), abi.encodeCall(Vm.load, (address(101), bytes32(uint256(23)))));
        assert(gasUsed == 125);
    }

    function testGasStoreWarmVM() public {
        // Load the vm into the set of accessed accounts. Should make the
        // following call to vm.store() cheaper
        (payable(address(vm)).send(0));

        // Call vm.store(address(101), bytes32(uint256(23)), bytes32(uint256(5)));
        uint256 gasUsed = measureGasForCall(address(vm), abi.encodeCall(Vm.store, (address(101), bytes32(uint256(23)), bytes32(uint256(5)))));
        assert(gasUsed == 125);
    }

    function testGasLoadWarmUp() public {
        // Check that vm.load(addr, slot) loads addr into the set of accessed
        // accounts, making subsequent access to addr cheaper
        vm.load(address(101), bytes32(uint256(23)));

        uint256 gasUsed = measureGasForCall(address(101), "");
        assert(gasUsed == 125);
    }


    function testGasStoreWarmUp() public {
        // Check that vm.store(addr, slot, val) loads addr into the set of accessed
        // accounts, making subsequent access to addr cheaper
        vm.store(address(101), bytes32(uint256(23)), bytes32(uint256(5)));

        uint256 gasUsed = measureGasForCall(address(101), "");
        assert(gasUsed == 125);
    }


    function measureGasForCall(address target, bytes memory callData) internal returns(uint256) {
        // Use assembly to measure gas cost as this gives more predictable
        // results than when using Solidity

        uint256 gasUsed;
        assembly {
            let dataPtr := add(32, callData)
            let dataSize := mload(callData)
            let g := gas()
            let r := call(g, target, 0, dataPtr, dataSize, 0, 0)
            gasUsed := sub(g, gas())
        }

        return gasUsed;
    }
}
