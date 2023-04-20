// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract SignTest is Test {

    function testSign() public {
        address alice = vm.addr(1);
        bytes32 hash = keccak256("Signed by Alice");
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(1, hash);
        address signer = ecrecover(hash, v, r, s);
        assertEq(alice, signer);
    }

    function testSign_symbolic(uint256 pk) public {
        vm.assume(pk != 0);
        vm.assume(pk < 115792089237316195423570985008687907852837564279074904382605163141518161494337);
        address fromPk = vm.addr(pk);
        bytes32 hash = keccak256("Signed by private key");
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, hash);
        address signer = ecrecover(hash, v, r, s);
        assertEq(fromPk, signer);
    }
}
