pragma solidity 0.5.0;
contract storagevar03 {
    uint private n;

    function execute() public returns(uint) {
        n = 5;
        require(false);
    }
}

