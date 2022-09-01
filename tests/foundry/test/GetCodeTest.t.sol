// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "src/MyToken.sol";


contract GetCodeTest is Test {
    MyToken myToken;


    function setUp() public{
        myToken = new MyToken(address(1234));
    }

    function testGetCode() public {
        bytes memory args = abi.encode(address(1234));
        vm.label(address(1234), "exampleAddress");
        bytes memory bytecode = abi.encodePacked(vm.getCode("MyToken.sol:MyToken"), args);
        address anotherAddress;
        assembly {
            anotherAddress := create(0, add(bytecode, 0x20), mload(bytecode))
        }

        assertEq0(address(myToken).code, anotherAddress.code);
    }

}
