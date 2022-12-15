// SPDX-License-Identifier: MIT
pragma solidity >=0.6.2 <0.9.0;
pragma experimental ABIEncoderV2;

import {Vm2} from "./Vm2.sol";

abstract contract KEVMCheats {

    Vm2 public constant kevm = Vm2(address(uint160(uint256(keccak256("hevm cheat code")))));

    // Checks if an address matches one of the built-in addresses.
    function notBuiltinAddress(address addr) internal pure returns (bool) {
        return (addr != address(645326474426547203313410069153905908525362434349) &&
                addr != address(1032069922050249630382865877677304880282300743300));
    }
}