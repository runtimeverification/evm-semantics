pragma solidity 0.4.24;
contract requires01 {
    function execute(uint256 a0) public returns (address) {
        require(a0 > 0);
        return 5;
    }
}

