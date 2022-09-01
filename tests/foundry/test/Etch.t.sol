// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "src/Token.sol";

contract EtchTest is Test {

    Token awesomeContract;

    function setUp() public{
        awesomeContract = new Token();
    }

    function testEtch() public {
        bytes memory code = address(awesomeContract).code;
        address targetAddr = address(1);
        vm.etch(targetAddr, code);
        assertEq(address(targetAddr).code, code);
    }
}
