// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "src/Token.sol";

contract EtchTest is Test {

    function testEtchConcrete() public {
        Token awesomeContract = new Token();
        bytes memory code = bytes("this should be EVM bytecode");
        vm.etch(address(awesomeContract), code);
        assertEq(address(awesomeContract).code, code);
    }

    function testEtchSymbolic(bytes calldata code) public {
        Token awesomeContract = new Token();
        vm.etch(address(awesomeContract), code);
        assertEq(address(awesomeContract).code, code);
    }

    function testEtchNonExistingAccount() public {
        bytes memory code = abi.encodePacked("my code");
        vm.etch(address(0), code);
        assert(address(0).codehash == keccak256(code));
    }

}
