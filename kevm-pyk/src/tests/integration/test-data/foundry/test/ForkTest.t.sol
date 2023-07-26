// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract ForkTest is Test {

    function testCreateFork() public {
        uint256 forkId = vm.createFork("https://eth-mainnet.public.blastapi.io");
        vm.selectFork(forkId);

        assertGt(block.number, 15223854); // as of time of writing
    }

    function testCreateForkBlock() public {
        uint256 forkId = vm.createFork("https://eth-mainnet.public.blastapi.io", 15223849);
        vm.selectFork(forkId);

        assertEq(block.number, 15223849);
    }

    function testCreateSelectFork() public {
        vm.createSelectFork("https://eth-mainnet.public.blastapi.io");
        assertGt(block.number, 15223854);
    }

    function testCreateSelectForkBlock() public {
        vm.createSelectFork("https://eth-mainnet.public.blastapi.io", 15223849);
        assertEq(block.number, 15223849);
    }

    function testActiveFork() public {
        uint256 mainnetForkId = vm.createFork("https://eth-mainnet.public.blastapi.io");
        uint256 binanceForkId = vm.createFork("https://bscrpc.com");

        assert(mainnetForkId != binanceForkId);

        vm.selectFork(mainnetForkId);
        assertEq(vm.activeFork(), mainnetForkId);

        vm.selectFork(binanceForkId);
        assertEq(vm.activeFork(), binanceForkId);
    }

    function testRollFork() public {
        uint256 forkId = vm.createFork("https://bscrpc.com");
        vm.selectFork(forkId);

        assertGt(block.number, 19918933); //
        vm.rollFork(19918777);

        assertEq(block.number, 19918777);
    }

    function testRollForkId() public {
        uint256 forkId = vm.createFork("https://api.avax.network/ext/bc/C/rpc");
        vm.rollFork(forkId, 17871134);

        vm.selectFork(forkId);
        //console.log(block.number);
        assertEq(block.number, 17871134);
    }

    function testRPCUrl() public {
        string memory url = vm.rpcUrl("optimism");
        assertEq(url, "https://optimism.alchemyapi.io/v2/...");
    }

    function testRPCUrlRevert() public {
        vm.expectRevert("Failed to resolve env var `RPC_MAINNET`: environment variable not found");
        vm.rpcUrl("mainnet");
    }

    function testAllRPCUrl() public {
        //this line is to comment after I know how to set the environment variable RPC_MAINNET
        vm.expectRevert("Failed to resolve env var `RPC_MAINNET`: environment variable not found");
        string[2][] memory allUrls = vm.rpcUrls();
        assertEq(allUrls.length, 2);

        string[2] memory val = allUrls[0];
        assertEq(val[0], "mainnet");

        string[2] memory env = allUrls[1];
        assertEq(env[0], "optimism");
    }
}
