// SPDX-License-Identifier: UNLICENSED
pragma solidity =0.8.13;

contract Token {
    uint256 x;
    mapping(address => uint256) balances;
    mapping(address => mapping(address => uint256)) allowances;
    string name;
    uint64 y;
    uint96 z;
    uint32 a;

    struct Foo {
        uint256 bar;
        address baz;
        uint48 boo;
        uint48 frob;
        uint48[] bills;
    }

    mapping(address => Foo) foos;

    function _move(address src, address dst, uint256 amount) internal {
        balances[src] = balances[src] - amount;
        balances[dst] = balances[dst] + amount;
    }

    function transfer(address dst, uint256 amount) external {
        _move(msg.sender, dst, amount);
    }
}
