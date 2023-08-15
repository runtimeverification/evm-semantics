// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract MyContract {
	uint256 public value;
}

contract ArrayTest is Test, KEVMCheats { 
	function testArrayInitialization() public {
		kevm.infiniteGas();

		MyContract myContract = new MyContract();
		kevm.symbolicStorage(address(myContract));

		vm.assume(myContract.value() == 3);

		bytes32[] memory array = new bytes32[](2 ** myContract.value());

		assertEq(array.length, 8);
	}
}
