pragma solidity ^0.8.13;

import "forge-std/Test.sol";

contract ContractAssert {
    function f() public pure {
        assert(false);
    }
}

contract ContractAssertTest is Test {
    ContractAssert c;

    function test_call_empty_account() public view{
        c.f();
    }
}