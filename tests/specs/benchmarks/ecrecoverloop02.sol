pragma solidity 0.5.0;
contract ecrecoverloop02 {
    function execute(bytes32 hash, bytes memory data,
                     uint8[2] memory sigV, bytes32[2] memory sigR, bytes32[2] memory sigS) pure public {
        for (uint i = 0; i < 2; i++) {
            address recovered = ecrecover(hash, sigV[i], sigR[i], sigS[i]);
            require(recovered > address(0));
        }
    }
}