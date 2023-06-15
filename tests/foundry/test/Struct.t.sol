pragma solidity =0.8.13;

import "forge-std/Test.sol";

contract StructTest is Test {
    struct Data {
        uint256 x;
        address a;
        uint8 y;
    }

    function compare(Data memory data) public {
        assertGt(data.x, uint256(uint160(data.a)));
        assertGt(uint256(uint160(data.a)), uint256(data.y));
    }
}
