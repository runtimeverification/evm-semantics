pragma solidity 0.4.24;
pragma experimental ABIEncoderV2;

contract structarg01 {
    struct Var {
        uint a;
        bytes b;
    }

    function execute(Var p) public returns (uint) {
        return p.a;
    }
}
