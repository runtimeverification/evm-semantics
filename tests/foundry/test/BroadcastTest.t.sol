// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "src/TestNumber.sol";
import "forge-std/Test.sol";

contract BroadcastTest is Test {
    address ACCOUNT_A;
    address ACCOUNT_B;

    function setUp() public {
        ACCOUNT_A = 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8;
        ACCOUNT_B = 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D;
    }

    function testDeploy() public {
        vm.broadcast(ACCOUNT_A);
        TestNumber test = new TestNumber(10);
        // this won't generate tx to sign
        uint256 b = test.t(4);
        assertEq(b,0);
        // this will
        vm.broadcast(ACCOUNT_B);
        test.t(5);
    }

    function deployOther() public {
        vm.startBroadcast(ACCOUNT_A);
        TestNumber test = new TestNumber(10);

        // will trigger a transaction
        test.t(1);

        vm.stopBroadcast();
    }

    function deployNoArgs() public {
        // broadcast the next call
        vm.broadcast();
        TestNumber test1 = new TestNumber(5);
        test1.t(0);

        // broadcast all calls between this line and `stopBroadcast`
        vm.startBroadcast();
        TestNumber test2 = new TestNumber(20);
        test2.t(25);
        vm.stopBroadcast();
}
}
