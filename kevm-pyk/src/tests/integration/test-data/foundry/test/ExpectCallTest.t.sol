// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

import "forge-std/Test.sol";
import "../src/KEVMCheats.sol";

contract Dummy {
    function numberA() public pure returns (uint) {
        return 200;
    }
}

contract ExpectCallTest is Test, KEVMCheats {


    function testExpectStaticCall() public {
        Dummy dummyContract = new Dummy();
        address addr = address(dummyContract);
        bytes memory data = abi.encodeWithSelector(dummyContract.numberA.selector);
        uint256 result = 0;
        kevm.expectStaticCall(addr, data);

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
        kevm.expectRegularCall(addr, 0, data);

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