Cryptographic Primitives
========================

Here we implement the various cryptographic primitives needed for KEVM.

```{.k .uiuck .rvk}
module KRYPTO
    imports STRING-SYNTAX
```

-   `Keccak256` takes a string and returns a 64-character hex-encoded string of the 32-byte keccak256 hash of the string.
-   `Sha256' takes a String and returns a 64-character hex-encoded string of the 32-byte SHA2-256 hash of the string.
-   `RipEmd160' takes a String and returns a 40-character hex-encoded string of the 20-byte RIPEMD160 hash of the string.
-   `ECDSARecover` takes a 32-character byte string of a message, v, r, s of the signed message and returns the 64-character public key used to sign the message.
    See [this StackOverflow post](https://ethereum.stackexchange.com/questions/15766/what-does-v-r-s-in-eth-gettransactionbyhash-mean) for some information about v, r, and s.

```{.k .uiuck .rvk}
    syntax String ::= Keccak256 ( String )                            [function, hook(KRYPTO.keccak256)]
                    | ECDSARecover ( String , Int , String , String ) [function, hook(KRYPTO.ecdsaRecover)]
                    | Sha256 ( String )                               [function, hook(KRYPTO.sha256)]
                    | RipEmd160 ( String )                            [function, hook(KRYPTO.ripemd160)]
endmodule
```
