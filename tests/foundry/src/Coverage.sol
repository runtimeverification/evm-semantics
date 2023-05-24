pragma solidity =0.8.13;

contract Coverage {
    function f(uint256 x) public pure returns (uint256) {
        if (x < 10) {
            return 0;
        } else if (x >= 10 && x < 20) {
            return 5;
        } else {
            return 10;
        }
    }
}
