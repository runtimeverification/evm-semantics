pragma solidity 0.4.24;
pragma experimental ABIEncoderV2;

contract structarg01 {
    struct Var {
        bytes a;
        uint b;
        uint256 c;
    }

    function execute(Var p) public returns (uint) {
        return p.a;
    }
}
