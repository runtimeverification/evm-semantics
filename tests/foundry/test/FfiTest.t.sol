// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract FfiTest is Test {
    
    function setUp() public{
        string memory key = "FOO";
        string memory val = "0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000a72756e74696d6556617200000000000000000000000000000000000000000000";
        vm.setEnv(key, val);
    }

    function testffi() public {
        string[] memory inputs = new string[](3);
        inputs[0] = "echo";
        inputs[1] = "-n";
        // ABI encoded "gm", as a string
        inputs[2] = vm.toString(abi.encode("gm"));
        //inputs[2] = "0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000002676d000000000000000000000000000000000000000000000000000000000000";
        bytes memory res = vm.ffi(inputs);
        string memory output = abi.decode(res, (string));
        assertEq(output, "gm");
    }


    function testFFIFOO() public {
        string[] memory inputs = new string[](3);
        inputs[0] = "bash";
        inputs[1] = "-c";
        inputs[2] = "echo -n $FOO";

        bytes memory res = vm.ffi(inputs);
        string memory output = abi.decode(res, (string));
        assertEq(output, "runtimeVar");
    }

    function testFFIScript() public {
        string[] memory inputs = new string[](2);
        inputs[0] = "bash";
        inputs[1] = "test/myscript.sh";

        bytes memory res = vm.ffi(inputs);
        string memory output = abi.decode(res, (string));
        assertEq(output, "runtimeVar");
    }

    function testFFIScript2() public {
        string[] memory inputs = new string[](2);
        inputs[0] = "bash";
        inputs[1] = "test/script.sh";

        bytes memory res = vm.ffi(inputs);
        string memory output = abi.decode(res, (string));
        assertEq(output, "true");
    }
}