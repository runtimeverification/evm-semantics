// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

contract ExpectEmit {
    event Transfer(address indexed from, address indexed to, uint256 amount);

    function t() public {
        emit Transfer(msg.sender, address(1337), 1337);
    }
}
