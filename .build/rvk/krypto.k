module KRYPTO
    imports STRING-SYNTAX
    // takes a string and returns a 64-character hex-encoded string of the 32-byte keccak256 hash of the string
    syntax String ::= Keccak256(String) [function, hook(KRYPTO.keccak256)]

    syntax String ::= Sha256(String) [function, hook(KRYPTO.sha256)]

    syntax String ::= RipEmd160(String) [function, hook(KRYPTO.ripemd160)]

    // takes a 32-character byte string of a message, and v, r, s of the signed message and returns the 64-character public key used to sign the message.
    syntax String ::= ECDSARecover(String, Int, String, String) [function, hook(KRYPTO.ecdsaRecover)]
endmodule

