pragma solidity 0.5.0;
contract staticloop00 {
    function execute(uint a0) pure external returns(uint256) {
        uint sum = a0;
        require (a0 < 10);
        for (uint i = 0; i < 3; i++) {
            sum += i;
        }
        return sum;
    }
}
