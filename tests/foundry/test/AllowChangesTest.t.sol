// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract ValueStore {
	uint256 public value1;
	uint256 public value2;

	function changeValue1(uint256 newValue) public {
		value1 = newValue;
	}

	function changeValue2(uint256 newValue) public {
		value2 = newValue;
	}
}

contract AllowChangesTest is Test, KEVMCheats {
	function test() public {
		assertTrue(true);
	}
	
	function testAllow(uint256 newValue) public {
		ValueStore canChange = new ValueStore();
		ValueStore cannotChange = new ValueStore();

		kevm.allowCallsToAddress(address(canChange));
		kevm.allowChangesToStorage(address(canChange), 0);

		canChange.changeValue1(newValue);
	}

	function testFailAllowCallsToAddress(uint256 newValue) public {
		ValueStore canChange = new ValueStore();
		ValueStore cannotChange = new ValueStore();

		kevm.allowCallsToAddress(address(canChange));
		kevm.allowChangesToStorage(address(canChange), 0);

		cannotChange.changeValue1(newValue);
	}

	function testFailAllowChangesToStorage(uint256 newValue) public {
		ValueStore canChange = new ValueStore();
		ValueStore cannotChange = new ValueStore();

		kevm.allowCallsToAddress(address(canChange));
		kevm.allowChangesToStorage(address(canChange), 0);

		canChange.changeValue2(newValue);
	}

	function testAllow_fail(uint256 newValue) public {
		ValueStore canChange = new ValueStore();
		ValueStore cannotChange = new ValueStore();

		kevm.allowCallsToAddress(address(canChange));
		kevm.allowChangesToStorage(address(canChange), 0);

		canChange.changeValue1(newValue);
	}
}