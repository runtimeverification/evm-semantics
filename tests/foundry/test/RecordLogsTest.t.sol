// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "src/EmitContract.sol";

contract RecordLogsTest is Test {
    ExpectEmit emitter;

    function setUp() public {
        emitter = new ExpectEmit();
        vm.recordLogs();
    }

    function testRecordLogs() public{
        emitter.t();
        Vm.Log[] memory entries = vm.getRecordedLogs();
        assertEq(entries.length, 1);
        assertEq(entries[0].topics[0], keccak256("Transfer(address,address,uint256)"));
        assertEq(abi.decode(entries[0].data, (uint256)), 1337);
    }
}
