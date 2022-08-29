// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract FilesTest is Test {

    function testReadWriteFile() public {
        string memory contents = vm.readFile("./test/file.txt");
        vm.writeFile("./test/filecopy.txt", contents);
        string memory contentsCopy = vm.readFile("./test/filecopy.txt");

        assertEq(contents, contentsCopy);
    }

    function testReadWriteLine() public {
        string memory line = vm.readLine("./test/file.txt");
        vm.writeLine("./test/fileline.txt", line);
        line = vm.readLine("./test/file.txt");
        assertEq(line, "for testing");

        vm.closeFile("./test/file.txt");
        line = vm.readLine("./test/file.txt");
        assertEq(line, "This is a file");
    }

    function testFailRemoveFile() public {
        string memory contents = vm.readFile("./test/file.txt");
        vm.writeFile("./test/filecopy2.txt", contents);
        vm.removeFile("./test/filecopy2.txt");
        vm.readFile("./test/filecopy2.txt");
    }
}
