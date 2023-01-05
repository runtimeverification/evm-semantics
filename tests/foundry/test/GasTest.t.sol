// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract GasTest is Test, KEVMCheats {
    function testSetGas() public {
        kevm.setGas(333000);
        uint256 gasLeft = gasleft();
        assertEq(gasLeft, 333000);
    }
}
