// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract ToStringTest is Test {

    function testAddressToString() public {
        address addr = 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8;
        string memory addrStr = vm.toString(addr);
        assertEq("0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8", addrStr);
    }

    function testBytesToString() public {
        bytes memory bts = hex"7109709ecfa91a80626ff3989d68f67f5b1dd12d";
        string memory btsStr = vm.toString(bts);
        assertEq("0x7109709ecfa91a80626ff3989d68f67f5b1dd12d", btsStr);
    }

    function testBytes32ToString() public {
        bytes32 bts = 0x00;
        string memory btsStr = vm.toString(bts);
        assertEq("0x0000000000000000000000000000000000000000000000000000000000000000", btsStr);
    }

    function testBoolToString() public {
        string memory boolStr = vm.toString(true);
        assertEq("true", boolStr);
        boolStr = vm.toString(false);
        assertEq("false", boolStr);
    }

    function testUint256ToString() public {
        uint256 number = 1234;
        string memory numberStr = vm.toString(number);
        assertEq("1234", numberStr);
    }

    function testIntToString() public {
        int number = -1234;
        string memory numberStr = vm.toString(number);
        assertEq("-1234", numberStr);
    }
}