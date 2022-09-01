// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

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

    function testAddr() public{
        address alice = vm.addr(1);
        assertEq(alice, 0x7E5F4552091A69125d5DfCb7b8C2659029395Bdf);
    }

}
