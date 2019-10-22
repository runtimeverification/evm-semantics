pragma solidity 0.5.0;
contract overflow00 {
    function execute(uint a0) public returns(uint) {
        uint n = a0 + 1;
        return n;
    }
}