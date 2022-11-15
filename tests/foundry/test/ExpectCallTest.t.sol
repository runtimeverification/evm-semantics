// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/Vm2.sol";

contract Dummy {
    function numberA() public pure returns (uint) {
        return 200;
    }
}

contract ExpectCallTest is Test {
    address constant private VM_ADDRESS =
        address(bytes20(uint160(uint256(keccak256('hevm cheat code')))));
    Vm2 public constant vm2 = Vm2(VM_ADDRESS);

    function testExpectStaticCall() public {
        Dummy dummyContract = new Dummy();
        address addr = address(dummyContract);
        bytes memory data = abi.encodeWithSelector(dummyContract.numberA.selector);
        uint256 result = 0;
        vm2.expectStaticCall(addr, data);

        assembly {
            let status := staticcall(16000, addr, add(data, 32), mload(data), 0, 0)
            if eq(status, 1) {
                if eq(returndatasize(), 32) {
                    returndatacopy(0, 0, 32)
                    result := mload(0)
                }
            }
        }

        assert(result == 200);
    }

    function testExpectRegularCall() public {
        Dummy dummyContract = new Dummy();
        address addr = address(dummyContract);
        bytes memory data = abi.encodeWithSelector(dummyContract.numberA.selector);
        uint256 result = 0;
        vm2.expectRegularCall(addr, data);

        assembly {
            let status := call(16000, addr, 0, add(data, 32), mload(data), 0, 0)
            if eq(status, 1) {
                if eq(returndatasize(), 32) {
                    returndatacopy(0, 0, 32)
                    result := mload(0)
                }
            }
        }

        assert(result == 200);
    }
}