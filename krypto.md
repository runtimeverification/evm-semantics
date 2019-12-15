Cryptographic Primitives
========================

Here we implement the various cryptographic primitives needed for KEVM.

```k
module KRYPTO
    imports STRING-SYNTAX
    imports INT-SYNTAX
    imports LIST
```

-   `Keccak256` takes a string and returns a 64-character hex-encoded string of the 32-byte keccak256 hash of the string.
-   `Sha256` takes a String and returns a 64-character hex-encoded string of the 32-byte SHA2-256 hash of the string.
-   `RipEmd160` takes a String and returns a 40-character hex-encoded string of the 20-byte RIPEMD160 hash of the string.
-   `ECDSARecover` takes a 32-character byte string of a message, v, r, s of the signed message and returns the 64-character public key used to sign the message.
-   `ECDSASign` takes a 32-character byte string of a message hash, a 32-character byte string of a private key, and returns the 65 byte hex-encoded signature in [r,s,v] form
-   `ECDSAPubKey` takes a 32-character byte string of a private key, and returns the 64 byte hex-encoded public key
    See [this StackOverflow post](https://ethereum.stackexchange.com/questions/15766/what-does-v-r-s-in-eth-gettransactionbyhash-mean) for some information about v, r, and s.

In all functions above, input `String` is interpreted as byte array, e.g. it is NOT hex-encoded.

```k
    syntax String ::= Keccak256 ( String )                            [function, hook(KRYPTO.keccak256)]
                    | ECDSARecover ( String , Int , String , String ) [function, hook(KRYPTO.ecdsaRecover)]
                    | Sha256 ( String )                               [function, hook(KRYPTO.sha256)]
                    | RipEmd160 ( String )                            [function, hook(KRYPTO.ripemd160)]
                    | ECDSASign ( String, String )                    [function, hook(KRYPTO.ecdsaSign)]
                    | ECDSAPubKey ( String )                          [function, hook(KRYPTO.ecdsaPubKey)]
                    | Blake2Compress ( String )                       [function, hook(KRYPTO.blake2compress)]
 // ---------------------------------------------------------------------------------------------------------
```

The BN128 elliptic curve is defined over 2-dimensional points over the fields of zero- and first-degree polynomials modulo a large prime. (x, y) is a point on G1, whereas (x1 x x2, y1 x y2) is a point on G2, in which x1 and y1 are zero-degree coefficients and x2 and y2 are first-degree coefficients. In each case, (0, 0) is used to represent the point at infinity.

-   `BN128Add` adds two points in G1 together,
-   `BN128Mul` multiplies a point in G1 by a scalar.
-   `BN128AtePairing` accepts a list of points in G1 and a list of points in G2 and returns whether the sum of the product of the discrete logarithm of the G1 points multiplied by the discrete logarithm of the G2 points is equal to zero.
-   `isValidPoint` takes a point in either G1 or G2 and validates that it actually falls on the respective elliptic curve.

```k
    syntax G1Point ::= "(" Int "," Int ")" [prefer]
    syntax G2Point ::= "(" Int "x" Int "," Int "x" Int ")"
    syntax G1Point ::= BN128Add(G1Point, G1Point) [function, hook(KRYPTO.bn128add)]
                     | BN128Mul(G1Point, Int)     [function, hook(KRYPTO.bn128mul)]
 // -------------------------------------------------------------------------------

    syntax Bool ::= BN128AtePairing(List, List) [function, hook(KRYPTO.bn128ate)]
 // -----------------------------------------------------------------------------

    syntax Bool ::= isValidPoint(G1Point) [function, hook(KRYPTO.bn128valid)]
                  | isValidPoint(G2Point) [function, klabel(isValidG2Point), hook(KRYPTO.bn128g2valid)]
 // ---------------------------------------------------------------------------------------------------
endmodule
```
