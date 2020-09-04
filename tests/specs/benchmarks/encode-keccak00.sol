pragma solidity 0.4.24;
contract encode_keccak00 {
    function execute(bytes32 a0, bytes32 a1) pure external returns(bytes32) {
        return keccak256(abi.encode(a0, a1));
    }
}