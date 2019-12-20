pragma solidity ^0.5.0;

import "./openzeppelin-contracts/contracts/token/ERC20/ERC20.sol";

contract test {

    function test_transfer(ERC20 token, address a2, uint256 amount) public {
        address a1 = address(this);

        require(a1 != address(0));
        require(a2 != address(0));
        require(a1 != a2);

        uint256 b1 = token.balanceOf(a1);
        uint256 b2 = token.balanceOf(a2);

        bool res = token.transfer(a2, amount);

        if (res) {
            uint256 b1n = token.balanceOf(a1);
            uint256 b2n = token.balanceOf(a2);
            assert(b1n == b1 - amount);
            assert(b2n == b2 + amount);
            assert(b1n <= b1);
            assert(b2n >= b2);
        }
    }

}
