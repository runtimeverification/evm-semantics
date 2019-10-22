pragma solidity 0.5.0;
contract encodepacked_keccak01 {
    function execute(bytes32 a0) pure external returns(bytes32) {
        return keccak256(abi.encodePacked(byte(0x01), a0));
    }
}