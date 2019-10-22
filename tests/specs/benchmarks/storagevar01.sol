pragma solidity 0.5.0;
contract storagevar01 {
    uint private n;

    function execute() public returns(uint) {
        n = 5;
        return n;
    }
}