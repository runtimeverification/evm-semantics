// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract GasTest is Test, KEVMCheats {
    function testSetGas() public {
        kevm.infiniteGas();
        uint256 gasLeftBefore = gasleft();
        uint256 gasLeftAfter  = gasleft();
        assert(gasLeftBefore <= gasLeftAfter);
    }
}
