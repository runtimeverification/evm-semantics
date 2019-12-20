pragma solidity ^0.4.19;

// from https://etherscan.io/address/0xc5d105e63711398af9bbff092d4b6769c82f793d#code
import "./BecToken.sol";

contract test {

    function test_batchTransfer(BecToken token, address a2, address a3, uint256 value) public {
        address a1 = address(this);

        require(a1 != a2);
        require(a1 != a3);
        require(a2 != a3);

        uint256 b1 = token.balanceOf(a1);
        uint256 b2 = token.balanceOf(a2);
        uint256 b3 = token.balanceOf(a3);

        address[] memory receivers = new address[](2);
        receivers[0] = a2;
        receivers[1] = a3;
        bool res = token.batchTransfer(receivers, value);

        if (res) {
            uint256 b1n = token.balanceOf(a1);
            uint256 b2n = token.balanceOf(a2);
            uint256 b3n = token.balanceOf(a3);
            assert(b1n == b1 - value - value);
            assert(b2n == b2 + value);
            assert(b3n == b3 + value);
            assert(b1n <= b1);
            assert(b2n >= b2);
            assert(b3n >= b3);
        }
    }

}
