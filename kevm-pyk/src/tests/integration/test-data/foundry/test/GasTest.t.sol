// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract GasTest is Test, KEVMCheats {
    function testInfiniteGas() public {
        kevm.infiniteGas();
        uint256 gasLeftBefore = gasleft();
        uint256 x = 345;
        uint256 y = 928;
        uint256 z = y - x;
        uint256 gasLeftAfter  = gasleft();
        assert(gasLeftBefore <= gasLeftAfter);
        assert(gasLeftAfter <= gasLeftBefore);
    }
}
