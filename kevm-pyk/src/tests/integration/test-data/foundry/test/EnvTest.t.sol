// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract EnvTest is Test {

    function testEnvBool() public {
        string memory key = "BOOL_VALUE";
        string memory val = "true";
        vm.setEnv(key, val);

        bool expected = true;
        bool output = vm.envBool(key);
        assert(output == expected);
    }

    function testEnvUInt() public {
        string memory key = "UINT_VALUE";
        string memory val = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
        vm.setEnv(key, val);

        uint256 expected = type(uint256).max;
        uint256 output = vm.envUint(key);
        assert(output == expected);
    }

    function testEnvInt() public {
        string memory key = "INT_VALUE";
        string memory val = "-57896044618658097711785492504343953926634992332820282019728792003956564819968";
        vm.setEnv(key, val);

        int256 expected = type(int256).min;
        int256 output = vm.envInt(key);
        assert(output == expected);
    }

    function testEnvAddress() public {
        string memory key = "ADDRESS_VALUE";
        string memory val = "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D";
        vm.setEnv(key, val);

        address expected = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
        address output = vm.envAddress(key);
        assert(output == expected);
    }

    function testEnvBytes32() public {
        string memory key = "BYTES32_VALUE";
        string memory val = "0x00";
        vm.setEnv(key, val);

        bytes32 expected = bytes32(0x0000000000000000000000000000000000000000000000000000000000000000);
        bytes32 output = vm.envBytes32(key);
        assert(output == expected);
    }

    function testEnvString() public {
        string memory key = "STRING_VALUE";
        string memory val = "hello, world!";
        vm.setEnv(key, val);

        string memory expected = "hello, world!";
        string memory output = vm.envString(key);
        assertEq(output, expected);
    }

    function testEnvBytes() public {
        string memory key = "BYTES_VALUE";
        string memory val = "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D";
        vm.setEnv(key, val);

        bytes memory expected = hex"7109709ECfa91a80626fF3989D68f67F5b1DD12D";
        bytes memory output = vm.envBytes(key);
        assertEq(output, expected);
    }

    function testEnvBoolArray() public {
        string memory key = "BOOL_VALUES";
        string memory val = "true,false,true,false";
        vm.setEnv(key, val);

        string memory delimiter = ",";
        bool[4] memory expected = [true, false, true, false];
        bool[] memory output = vm.envBool(key, delimiter);
        assert(keccak256(abi.encodePacked((output))) == keccak256(abi.encodePacked((expected))));
    }

    function testEnvUIntArray() public {
        string memory key = "UINT_VALUES";
        string memory val = "0,0x0000000000000000000000000000000000000000000000000000000000000000";
        vm.setEnv(key, val);

        string memory delimiter = ",";
        uint256[2] memory expected = [type(uint256).min, type(uint256).min];
        uint256[] memory output = vm.envUint(key, delimiter);
        assert(keccak256(abi.encodePacked((output))) == keccak256(abi.encodePacked((expected))));
    }

    function testEnvIntArray() public {
        string memory key = "INT_VALUES";
        string memory val = "-0x8000000000000000000000000000000000000000000000000000000000000000,+0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF";
        vm.setEnv(key, val);

        string memory delimiter = ",";
        int256[2] memory expected = [type(int256).min, type(int256).max];
        int256[] memory output = vm.envInt(key, delimiter);
        assert(keccak256(abi.encodePacked((output))) == keccak256(abi.encodePacked((expected))));
    }

    function testEnvAddresseArray() public {
        string memory key = "ADDRESS_VALUES";
        string memory val = "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D,0x0000000000000000000000000000000000000000";
        vm.setEnv(key, val);

        string memory delimiter = ",";
        address[2] memory expected = [
                0x7109709ECfa91a80626fF3989D68f67F5b1DD12D,
                0x0000000000000000000000000000000000000000
                ];
        address[] memory output = vm.envAddress(key, delimiter);
        assert(keccak256(abi.encodePacked((output))) == keccak256(abi.encodePacked((expected))));
    }

    function testEnvBytes32Array() public {
        string memory key = "BYTES32_VALUES";
        string memory val = "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D,0x00";
        vm.setEnv(key, val);

        string memory delimiter = ",";
        bytes32[2] memory expected = [
                bytes32(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D000000000000000000000000),
                bytes32(0x0000000000000000000000000000000000000000000000000000000000000000)
                ];
        bytes32[] memory output = vm.envBytes32(key, delimiter);
        assert(keccak256(abi.encodePacked((output))) == keccak256(abi.encodePacked((expected))));
    }

    function testEnvStringArray() public {
        string memory key = "STRING_VALUES";
        string memory val = "hello, world!|0x7109709ECfa91a80626fF3989D68f67F5b1DD12D";
        vm.setEnv(key, val);

        string memory delimiter = "|";
        string[2] memory expected = [
                "hello, world!",
                "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D"
            ];
        string[] memory output = vm.envString(key, delimiter);
        for (uint i = 0; i < expected.length; ++i) {
            assert(keccak256(abi.encodePacked((output[i]))) == keccak256(abi.encodePacked((expected[i]))));
        }
    }

    function testEnvBytesArray() public {
        string memory key = "BYTES_VALUES";
        string memory val = "0x7109709ECfa91a80626fF3989D68f67F5b1DD12D,0x00";
        vm.setEnv(key, val);

        string memory delimiter = ",";
        bytes[] memory expected = new bytes[](2);
        expected[0] = hex"7109709ECfa91a80626fF3989D68f67F5b1DD12D";
        expected[1] = hex"00";
        bytes[] memory output = vm.envBytes(key, delimiter);
        for (uint i = 0; i < expected.length; ++i) {
            assert(keccak256(abi.encodePacked((output[i]))) == keccak256(abi.encodePacked((expected[i]))));
        }
    }

}
