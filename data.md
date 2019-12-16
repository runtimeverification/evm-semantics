EVM Words
=========

```k
requires "krypto.k"
requires "evm-types.k"
requires "json.k"
requires "serialization.k"
```

```k
module EVM-DATA
    imports KRYPTO
    imports EVM-TYPES
    imports SERIALIZATION
    imports STRING-BUFFER
    imports MAP-SYMBOLIC
    imports COLLECTIONS
    imports JSON
```

```{.k .concrete .bytes}
    imports BYTES
```

-   `#lookup` looks up a key in a map and returns 0 if the key doesn't exist, otherwise returning its value.

```k
    syntax Int ::= #lookup ( Map , Int ) [function]
 // -----------------------------------------------
    rule [#lookup.some]: #lookup( (KEY |-> VAL) M, KEY ) => VAL
    rule [#lookup.none]: #lookup(               M, KEY ) => 0 requires notBool KEY in_keys(M)
```

```k
endmodule
```
