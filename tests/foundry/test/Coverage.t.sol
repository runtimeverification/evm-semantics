pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "src/KEVMCheats.sol";

import "src/Coverage.sol";

contract CoverageTest is Test, KEVMCheats {
    Coverage cov;

    function setUp() public {
        cov = new Coverage();
    }

    function test_f_1(uint256 x) public {
        vm.assume(x < 10);
        uint256 y = cov.f(x);
        assertEq(y, 0);
    }

    function test_f_2(uint256 x) public {
        vm.assume(x >= 10);
        vm.assume(x < 20);
        uint256 y = cov.f(x);
        assertEq(y, 5);
    }

    function test_f_3() public {
        uint256 y = cov.f(238);
        assertGt(y, 0);
    }

    address test_contract = address(1234567891011121314151617181920);

    function test_prank(address who) public {
        kevm.infiniteGas();
        vm.assume(who != 0xfcC345e00009B3E5dF2FCAFbe77B1Fd66e736a68); // address("notWho")
        vm.startPrank(who);
        test_contract.call(abi.encodeWithSignature("func()"));
    }

    function test_not_null_sig(bytes4 sig) public {
        vm.assume(sig != 0x00000000);
        test_contract.call(abi.encode(sig));
    }

    function test_simple(uint256 x) public {
        vm.assume(!(x > 10));
        vm.assume(x < 5);
        test_contract.call(abi.encodeWithSignature("func(uint256)", x));
    }

    function test_bool(bool x) public {
        vm.assume(!x == true);
        test_contract.call(abi.encodeWithSignature("func(bool)", x));
    }
}
