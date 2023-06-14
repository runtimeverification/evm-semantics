// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

struct Storage {
    uint slot0;
    uint slot1;
}

contract SnapshotTest is Test {
    Storage store;

    function setUp() public {
        store.slot0 = 10;
        store.slot1 = 20;
    }

    function testSnapshot() public {
        uint256 snapshot = vm.snapshot();
        store.slot0 = 300;
        store.slot1 = 400;

        assertEq(store.slot0, 300);
        assertEq(store.slot1, 400);

        // after resetting to a snapshot all changes are discarded
        vm.revertTo(snapshot);
        assertEq(store.slot0, 10, "snapshot revert for slot 0 unsuccessful");
        assertEq(store.slot1, 20, "snapshot revert for slot 1 unsuccessful");
    }

}

