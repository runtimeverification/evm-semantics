// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract AddrTest is Test, KEVMCheats {

    function test_addr_true() public {
        address alice = vm.addr(1);
        assertEq(alice, 0x7E5F4552091A69125d5DfCb7b8C2659029395Bdf);
    }

    function test_addr_false() public {
        address alice = vm.addr(0);
    }

    function testFail_addr_true() public {
        address alice = vm.addr(115792089237316195423570985008687907852837564279074904382605163141518161494337);
    }

    function testFail_addr_false() public {
        address alice = vm.addr(1);
        assertEq(alice, 0x7E5F4552091A69125d5DfCb7b8C2659029395Bdf);
    }

    function test_addr_symbolic(uint256 pk) public {
        vm.assume(pk != 0);
        vm.assume(pk < 115792089237316195423570985008687907852837564279074904382605163141518161494337);
        address alice = vm.addr(pk);
        assert(true);
    }

    function test_notBuiltinAddress_concrete() public {
       assertTrue(notBuiltinAddress(address(110)));
    }

    function test_notBuiltinAddress_symbolic(address addr) public {
        vm.assume(addr != address(728815563385977040452943777879061427756277306518));
        vm.assume(addr != address(645326474426547203313410069153905908525362434349));
        assertTrue(notBuiltinAddress(addr));
    }

    function test_builtInAddresses() public {
        assertEq(address(this), address(728815563385977040452943777879061427756277306518));
        assertEq(address(vm), address(645326474426547203313410069153905908525362434349));
    }
}
