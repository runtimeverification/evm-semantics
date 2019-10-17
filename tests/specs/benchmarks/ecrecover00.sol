pragma solidity 0.5.0;
contract ecrecover00 {
    function execute(bytes32 hash, uint8 sigV, bytes32 sigR, bytes32 sigS) pure external returns(address) {
        address recovered = ecrecover(hash, sigV, sigR, sigS);
        require(recovered > address(0));
        return recovered;
    }
}