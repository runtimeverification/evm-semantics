// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Test.sol";

contract FilesTest is Test {
    
    function testReadWriteFile() public {
        string memory contents = vm.readFile("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/file.txt");
        vm.writeFile("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/filecopy.txt", contents);
        string memory contentsCopy = vm.readFile("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/filecopy.txt");

        assertEq(contents, contentsCopy);
    }

    function testReadWriteLine() public {
        string memory line = vm.readLine("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/file.txt");
        vm.writeLine("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/filecopy.txt", line);
        line = vm.readLine("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/file.txt");
        assertEq(line, "for testing");
        
        vm.closeFile("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/file.txt");
        line = vm.readLine("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/file.txt");
        assertEq(line, "This is a file");
    }

    function testFailRemoveFile() public {
        vm.removeFile("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/filecopy.txt");
        vm.readFile("/Users/lisandrasilva/evm-semantics/tests/gen-spec/foundry/test/filecopy.txt");
    }
}