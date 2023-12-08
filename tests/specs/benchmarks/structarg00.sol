pragma solidity 0.4.24;
pragma experimental ABIEncoderV2;

contract structarg00 {
    struct Var {
        uint a;
        uint8 b;
    }

    function execute(Var p) public returns (uint) {
        return p.a;
    }
}
