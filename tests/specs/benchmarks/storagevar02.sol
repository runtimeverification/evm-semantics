pragma solidity 0.5.0;
contract storagevar02 {
    uint private n;

    function execute() public returns(uint) {
        n = n + 1;
        return n;
    }
}