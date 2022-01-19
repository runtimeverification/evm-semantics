pragma solidity >=0.6.0;

contract MyContract {

    uint256 x;

    function getX() public view returns (uint256) {
        return x;
    }

    function setX(uint256 _x) public {
        x = _x;
    }

    function maxInt(uint256 a, uint256 b) public pure returns (uint256) {
        if (a < b) {
            return b;
        }
        return a;
    }
}
