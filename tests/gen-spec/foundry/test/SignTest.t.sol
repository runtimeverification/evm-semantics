// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Test.sol";

contract SignTest is Test {
    
    function setUp() public{}

    function testSign() public {
        address alice = vm.addr(1);
        bytes32 hash = keccak256("Signed by Alice");
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(1, hash);
        address signer = ecrecover(hash, v, r, s);
        assertEq(alice, signer);
    }
}