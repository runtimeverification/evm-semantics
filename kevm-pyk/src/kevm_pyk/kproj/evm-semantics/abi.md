ABI Encoding
============

```k
requires "evm.md"
requires "buf.md"

module EVM-ABI
    imports EVM
    imports BUF
```

### ABI Call Data

When a function is called in the EVM, its arguments are encoded in a single byte-array and put in the so-called 'call data' section.
The encoding is defined in the [Ethereum contract application binary interface (ABI) specification](https://solidity.readthedocs.io/en/develop/abi-spec.html).
The eDSL provides `#abiCallData`, a notation to specify the ABI call data in a way similar to a high-level function call notation, defined below.
It specifies the function name and the (symbolic) arguments along with their types.
For example, the following notation represents a data that encodes a call to the `transfer` function with two arguments: `TO`, the receiver account address of type `address` (an 160-bit unsigned integer), and `VALUE`, the value to transfer of type `unit256` (a 256-bit unsigned integer).

```
  #abiCallData("transfer", #address(TO), #uint256(VALUE))
```

which denotes (indeed, is translated to) the following byte array:

```
  F1 : F2 : F3 : F4 : T1 : ... : T32 : V1 : ... : V32
```

where `F1 : F2 : F3 : F4` is the (two's complement) byte-array representation of `2835717307`, the first four bytes of the hash value of the `transfer` function signature, `keccak256("transfer(address,unit256)")`, and `T1 : ... : T32` and `V1 : ... : V32` are the byte-array representations of `TO` and `VALUE` respectively.

```k
    syntax TypedArg ::= #address ( Int )                        [klabel(abi_type_address), symbol]
                      | #uint256 ( Int )                        [klabel(abi_type_uint256), symbol]
                      | #uint248 ( Int )                        [klabel(abi_type_uint248), symbol]
                      | #uint240 ( Int )                        [klabel(abi_type_uint240), symbol]
                      | #uint232 ( Int )                        [klabel(abi_type_uint232), symbol]
                      | #uint224 ( Int )                        [klabel(abi_type_uint224), symbol]
                      | #uint216 ( Int )                        [klabel(abi_type_uint216), symbol]
                      | #uint208 ( Int )                        [klabel(abi_type_uint208), symbol]
                      | #uint200 ( Int )                        [klabel(abi_type_uint200), symbol]
                      | #uint192 ( Int )                        [klabel(abi_type_uint192), symbol]
                      | #uint184 ( Int )                        [klabel(abi_type_uint184), symbol]
                      | #uint176 ( Int )                        [klabel(abi_type_uint176), symbol]
                      | #uint168 ( Int )                        [klabel(abi_type_uint168), symbol]
                      | #uint160 ( Int )                        [klabel(abi_type_uint160), symbol]
                      | #uint152 ( Int )                        [klabel(abi_type_uint152), symbol]
                      | #uint144 ( Int )                        [klabel(abi_type_uint144), symbol]
                      | #uint136 ( Int )                        [klabel(abi_type_uint136), symbol]
                      | #uint128 ( Int )                        [klabel(abi_type_uint128), symbol]
                      | #uint120 ( Int )                        [klabel(abi_type_uint120), symbol]
                      | #uint112 ( Int )                        [klabel(abi_type_uint112), symbol]
                      | #uint104 ( Int )                        [klabel(abi_type_uint104), symbol]
                      | #uint96  ( Int )                        [klabel(abi_type_uint96),  symbol]
                      | #uint88  ( Int )                        [klabel(abi_type_uint88),  symbol]
                      | #uint80  ( Int )                        [klabel(abi_type_uint80),  symbol]
                      | #uint72  ( Int )                        [klabel(abi_type_uint72),  symbol]
                      | #uint64  ( Int )                        [klabel(abi_type_uint64),  symbol]
                      | #uint56  ( Int )                        [klabel(abi_type_uint56),  symbol]
                      | #uint48  ( Int )                        [klabel(abi_type_uint48),  symbol]
                      | #uint40  ( Int )                        [klabel(abi_type_uint40),  symbol]
                      | #uint32  ( Int )                        [klabel(abi_type_uint32),  symbol]
                      | #uint24  ( Int )                        [klabel(abi_type_uint24),  symbol]
                      | #uint16  ( Int )                        [klabel(abi_type_uint16),  symbol]
                      | #uint8   ( Int )                        [klabel(abi_type_uint8),   symbol]
                      | #int256  ( Int )                        [klabel(abi_type_int256),  symbol]
                      | #int248  ( Int )                        [klabel(abi_type_int248),  symbol]
                      | #int240  ( Int )                        [klabel(abi_type_int240),  symbol]
                      | #int232  ( Int )                        [klabel(abi_type_int232),  symbol]
                      | #int224  ( Int )                        [klabel(abi_type_int224),  symbol]
                      | #int216  ( Int )                        [klabel(abi_type_int216),  symbol]
                      | #int208  ( Int )                        [klabel(abi_type_int208),  symbol]
                      | #int200  ( Int )                        [klabel(abi_type_int200),  symbol]
                      | #int192  ( Int )                        [klabel(abi_type_int192),  symbol]
                      | #int184  ( Int )                        [klabel(abi_type_int184),  symbol]
                      | #int176  ( Int )                        [klabel(abi_type_int176),  symbol]
                      | #int168  ( Int )                        [klabel(abi_type_int168),  symbol]
                      | #int160  ( Int )                        [klabel(abi_type_int160),  symbol]
                      | #int152  ( Int )                        [klabel(abi_type_int152),  symbol]
                      | #int144  ( Int )                        [klabel(abi_type_int144),  symbol]
                      | #int136  ( Int )                        [klabel(abi_type_int136),  symbol]
                      | #int128  ( Int )                        [klabel(abi_type_int128),  symbol]
                      | #int120  ( Int )                        [klabel(abi_type_int120),  symbol]
                      | #int112  ( Int )                        [klabel(abi_type_int112),  symbol]
                      | #int104  ( Int )                        [klabel(abi_type_int104),  symbol]
                      | #int96   ( Int )                        [klabel(abi_type_int96),   symbol]
                      | #int88   ( Int )                        [klabel(abi_type_int88),   symbol]
                      | #int80   ( Int )                        [klabel(abi_type_int80),   symbol]
                      | #int72   ( Int )                        [klabel(abi_type_int72),   symbol]
                      | #int64   ( Int )                        [klabel(abi_type_int64),   symbol]
                      | #int56   ( Int )                        [klabel(abi_type_int56),   symbol]
                      | #int48   ( Int )                        [klabel(abi_type_int48),   symbol]
                      | #int40   ( Int )                        [klabel(abi_type_int40),   symbol]
                      | #int32   ( Int )                        [klabel(abi_type_int32),   symbol]
                      | #int24   ( Int )                        [klabel(abi_type_int24),   symbol]
                      | #int16   ( Int )                        [klabel(abi_type_int16),   symbol]
                      | #int8    ( Int )                        [klabel(abi_type_int8),    symbol]
                      | #bytes1  ( Int )                        [klabel(abi_type_bytes1),  symbol]
                      | #bytes2  ( Int )                        [klabel(abi_type_bytes2),  symbol]
                      | #bytes3  ( Int )                        [klabel(abi_type_bytes3),  symbol]
                      | #bytes4  ( Int )                        [klabel(abi_type_bytes4),  symbol]
                      | #bytes5  ( Int )                        [klabel(abi_type_bytes5),  symbol]
                      | #bytes6  ( Int )                        [klabel(abi_type_bytes6),  symbol]
                      | #bytes7  ( Int )                        [klabel(abi_type_bytes7),  symbol]
                      | #bytes8  ( Int )                        [klabel(abi_type_bytes8),  symbol]
                      | #bytes9  ( Int )                        [klabel(abi_type_bytes9),  symbol]
                      | #bytes10 ( Int )                        [klabel(abi_type_bytes10), symbol]
                      | #bytes11 ( Int )                        [klabel(abi_type_bytes11), symbol]
                      | #bytes12 ( Int )                        [klabel(abi_type_bytes12), symbol]
                      | #bytes13 ( Int )                        [klabel(abi_type_bytes13), symbol]
                      | #bytes14 ( Int )                        [klabel(abi_type_bytes14), symbol]
                      | #bytes15 ( Int )                        [klabel(abi_type_bytes15), symbol]
                      | #bytes16 ( Int )                        [klabel(abi_type_bytes16), symbol]
                      | #bytes17 ( Int )                        [klabel(abi_type_bytes17), symbol]
                      | #bytes18 ( Int )                        [klabel(abi_type_bytes18), symbol]
                      | #bytes19 ( Int )                        [klabel(abi_type_bytes19), symbol]
                      | #bytes20 ( Int )                        [klabel(abi_type_bytes20), symbol]
                      | #bytes21 ( Int )                        [klabel(abi_type_bytes21), symbol]
                      | #bytes22 ( Int )                        [klabel(abi_type_bytes22), symbol]
                      | #bytes23 ( Int )                        [klabel(abi_type_bytes23), symbol]
                      | #bytes24 ( Int )                        [klabel(abi_type_bytes24), symbol]
                      | #bytes25 ( Int )                        [klabel(abi_type_bytes25), symbol]
                      | #bytes26 ( Int )                        [klabel(abi_type_bytes26), symbol]
                      | #bytes27 ( Int )                        [klabel(abi_type_bytes27), symbol]
                      | #bytes28 ( Int )                        [klabel(abi_type_bytes28), symbol]
                      | #bytes29 ( Int )                        [klabel(abi_type_bytes29), symbol]
                      | #bytes30 ( Int )                        [klabel(abi_type_bytes30), symbol]
                      | #bytes31 ( Int )                        [klabel(abi_type_bytes31), symbol]
                      | #bytes32 ( Int )                        [klabel(abi_type_bytes32), symbol]
                      | #bool    ( Int )                        [klabel(abi_type_bool),    symbol]
                      | #bytes   ( Bytes )                      [klabel(abi_type_bytes),   symbol]
                      | #string  ( String )                     [klabel(abi_type_string),  symbol]
                      | #array   ( TypedArg , Int , TypedArgs ) [klabel(abi_type_array),   symbol]
                      | #tuple   ( TypedArgs )                  [klabel(abi_type_tuple),   symbol]
 // ----------------------------------------------------------------------------------------------

    syntax TypedArgs ::= List{TypedArg, ","} [symbol(typedArgs)]
 // ------------------------------------------------------------

    syntax Bytes ::= #abiCallData ( String , TypedArgs ) [klabel(#abiCallData), function]
 // -------------------------------------------------------------------------------------
    rule #abiCallData( FNAME , ARGS ) => #signatureCallData(FNAME, ARGS) +Bytes #encodeArgs(ARGS)

    syntax Bytes ::= #signatureCallData ( String, TypedArgs ) [klabel(#signatureCallData), function]
 // ------------------------------------------------------------------------------------------------
    rule #signatureCallData( FNAME , ARGS ) => #parseByteStack(substrString(Keccak256(String2Bytes(#generateSignature(FNAME, ARGS))), 0, 8))

    syntax String ::= #generateSignature     ( String, TypedArgs ) [klabel(#generateSignature), function, total]
                    | #generateSignatureArgs ( TypedArgs )         [klabel(#generateSignatureArgs),function, total]
 // --------------------------------------------------------------------------------------------------------------
    rule #generateSignature( FNAME , ARGS ) => FNAME +String "(" +String #generateSignatureArgs(ARGS) +String ")"

    rule #generateSignatureArgs(.TypedArgs)                            => ""
    rule #generateSignatureArgs(TARGA:TypedArg, .TypedArgs)            => #typeName(TARGA)
    rule #generateSignatureArgs(TARGA:TypedArg, TARGB:TypedArg, TARGS) => #typeName(TARGA) +String "," +String #generateSignatureArgs(TARGB, TARGS)

    syntax String ::= #typeName ( TypedArg ) [klabel(#typeName), function, total]
 // -----------------------------------------------------------------------------
    rule #typeName(   #address( _ )) => "address"

    rule #typeName(   #uint256( _ )) => "uint256"
    rule #typeName(   #uint248( _ )) => "uint248"
    rule #typeName(   #uint240( _ )) => "uint240"
    rule #typeName(   #uint232( _ )) => "uint232"
    rule #typeName(   #uint224( _ )) => "uint224"
    rule #typeName(   #uint216( _ )) => "uint216"
    rule #typeName(   #uint208( _ )) => "uint208"
    rule #typeName(   #uint200( _ )) => "uint200"
    rule #typeName(   #uint192( _ )) => "uint192"
    rule #typeName(   #uint184( _ )) => "uint184"
    rule #typeName(   #uint176( _ )) => "uint176"
    rule #typeName(   #uint168( _ )) => "uint168"
    rule #typeName(   #uint160( _ )) => "uint160"
    rule #typeName(   #uint152( _ )) => "uint152"
    rule #typeName(   #uint144( _ )) => "uint144"
    rule #typeName(   #uint136( _ )) => "uint136"
    rule #typeName(   #uint128( _ )) => "uint128"
    rule #typeName(   #uint120( _ )) => "uint120"
    rule #typeName(   #uint112( _ )) => "uint112"
    rule #typeName(   #uint104( _ )) => "uint104"
    rule #typeName(   #uint96( _ )) => "uint96"
    rule #typeName(   #uint88( _ )) => "uint88"
    rule #typeName(   #uint80( _ )) => "uint80"
    rule #typeName(   #uint72( _ )) => "uint72"
    rule #typeName(   #uint64( _ )) => "uint64"
    rule #typeName(   #uint56( _ )) => "uint56"
    rule #typeName(   #uint48( _ )) => "uint48"
    rule #typeName(   #uint40( _ )) => "uint40"
    rule #typeName(   #uint32( _ )) => "uint32"
    rule #typeName(   #uint24( _ )) => "uint24"
    rule #typeName(   #uint16( _ )) => "uint16"
    rule #typeName(   #uint8( _ )) => "uint8"

    rule #typeName(   #int256( _ )) => "int256"
    rule #typeName(   #int248( _ )) => "int248"
    rule #typeName(   #int240( _ )) => "int240"
    rule #typeName(   #int232( _ )) => "int232"
    rule #typeName(   #int224( _ )) => "int224"
    rule #typeName(   #int216( _ )) => "int216"
    rule #typeName(   #int208( _ )) => "int208"
    rule #typeName(   #int200( _ )) => "int200"
    rule #typeName(   #int192( _ )) => "int192"
    rule #typeName(   #int184( _ )) => "int184"
    rule #typeName(   #int176( _ )) => "int176"
    rule #typeName(   #int168( _ )) => "int168"
    rule #typeName(   #int160( _ )) => "int160"
    rule #typeName(   #int152( _ )) => "int152"
    rule #typeName(   #int144( _ )) => "int144"
    rule #typeName(   #int136( _ )) => "int136"
    rule #typeName(   #int128( _ )) => "int128"
    rule #typeName(   #int120( _ )) => "int120"
    rule #typeName(   #int112( _ )) => "int112"
    rule #typeName(   #int104( _ )) => "int104"
    rule #typeName(    #int96( _ )) => "int96"
    rule #typeName(    #int88( _ )) => "int88"
    rule #typeName(    #int80( _ )) => "int80"
    rule #typeName(    #int72( _ )) => "int72"
    rule #typeName(    #int64( _ )) => "int64"
    rule #typeName(    #int56( _ )) => "int56"
    rule #typeName(    #int48( _ )) => "int48"
    rule #typeName(    #int40( _ )) => "int40"
    rule #typeName(    #int32( _ )) => "int32"
    rule #typeName(    #int24( _ )) => "int24"
    rule #typeName(    #int16( _ )) => "int16"
    rule #typeName(     #int8( _ )) => "int8"

    rule #typeName(    #bytes1( _ )) => "bytes1"
    rule #typeName(    #bytes2( _ )) => "bytes2"
    rule #typeName(    #bytes3( _ )) => "bytes3"
    rule #typeName(    #bytes4( _ )) => "bytes4"
    rule #typeName(    #bytes5( _ )) => "bytes5"
    rule #typeName(    #bytes6( _ )) => "bytes6"
    rule #typeName(    #bytes7( _ )) => "bytes7"
    rule #typeName(    #bytes8( _ )) => "bytes8"
    rule #typeName(    #bytes9( _ )) => "bytes9"
    rule #typeName(   #bytes10( _ )) => "bytes10"
    rule #typeName(   #bytes11( _ )) => "bytes11"
    rule #typeName(   #bytes12( _ )) => "bytes12"
    rule #typeName(   #bytes13( _ )) => "bytes13"
    rule #typeName(   #bytes14( _ )) => "bytes14"
    rule #typeName(   #bytes15( _ )) => "bytes15"
    rule #typeName(   #bytes16( _ )) => "bytes16"
    rule #typeName(   #bytes17( _ )) => "bytes17"
    rule #typeName(   #bytes18( _ )) => "bytes18"
    rule #typeName(   #bytes19( _ )) => "bytes19"
    rule #typeName(   #bytes20( _ )) => "bytes20"
    rule #typeName(   #bytes21( _ )) => "bytes21"
    rule #typeName(   #bytes22( _ )) => "bytes22"
    rule #typeName(   #bytes23( _ )) => "bytes23"
    rule #typeName(   #bytes24( _ )) => "bytes24"
    rule #typeName(   #bytes25( _ )) => "bytes25"
    rule #typeName(   #bytes26( _ )) => "bytes26"
    rule #typeName(   #bytes27( _ )) => "bytes27"
    rule #typeName(   #bytes28( _ )) => "bytes28"
    rule #typeName(   #bytes29( _ )) => "bytes29"
    rule #typeName(   #bytes30( _ )) => "bytes30"
    rule #typeName(   #bytes31( _ )) => "bytes31"
    rule #typeName(   #bytes32( _ )) => "bytes32"

    rule #typeName(      #bool( _ )) => "bool"

    rule #typeName(     #bytes( _ )) => "bytes"

    rule #typeName(    #string( _ )) => "string"

    rule #typeName( #array(T, _, _)) => #typeName(T) +String "[]"

    rule #typeName(    #tuple(ARGS)) => "(" +String #generateSignatureArgs(ARGS) +String ")"

    syntax Bytes ::= #encodeArgs    ( TypedArgs )                       [klabel(#encodeArgs), function]
    syntax Bytes ::= #encodeArgsAux ( TypedArgs , Int , Bytes , Bytes ) [klabel(#encodeArgsAux), function]
 // ------------------------------------------------------------------------------------------------------
    rule #encodeArgs(ARGS) => #encodeArgsAux(ARGS, #lenOfHeads(ARGS), .Bytes, .Bytes)

    rule #encodeArgsAux(.TypedArgs, _:Int, HEADS, TAILS) => HEADS +Bytes TAILS

    rule #encodeArgsAux((ARG, ARGS), OFFSET, HEADS, TAILS)
        => #encodeArgsAux(ARGS, OFFSET, HEADS +Bytes #enc(ARG), TAILS)
      requires #isStaticType(ARG)

    rule #encodeArgsAux((ARG, ARGS), OFFSET, HEADS, TAILS)
        => #encodeArgsAux(ARGS, OFFSET +Int #sizeOfDynamicType(ARG), HEADS +Bytes #enc(#uint256(OFFSET)), TAILS +Bytes #enc(ARG))
      requires notBool(#isStaticType(ARG))
```

The `#lenOfHeads` is a recursive function used to calculate the space required for the 'head' of data structures in Solidity.
For most types, this is a fixed 32 bytes, except for static tuples, for which the length is the cumulative length of their contents.

```k
    syntax Int ::= #lenOfHeads ( TypedArgs ) [klabel(#lenOfHeads), function, total]
 // -------------------------------------------------------------------------------
    rule #lenOfHeads(.TypedArgs) => 0
    rule #lenOfHeads(ARG, ARGS)  => #lenOfHead(ARG) +Int #lenOfHeads(ARGS)

    syntax Int ::= #lenOfHead ( TypedArg ) [klabel(#lenOfHead), function, total]
 // ----------------------------------------------------------------------------
    rule #lenOfHead( #tuple( ARGS )) => #lenOfHeads(ARGS) requires #isStaticType(#tuple(ARGS))
    rule #lenOfHead(              _) => 32 [owise]
```

`#isStaticType` checks if a given `TypedArg` is a static type in order to determine if it has a fixed size.

```k
    syntax Bool ::= #isStaticType ( TypedArg ) [klabel(#isStaticType), function, total]
 // -----------------------------------------------------------------------------------
    rule #isStaticType(    #bytes( _ )) => false
    rule #isStaticType(   #string( _ )) => false
    rule #isStaticType(#array(_, _, _)) => false
    rule #isStaticType( #tuple( ARGS )) => notBool #hasDynamicType(ARGS)
    rule #isStaticType(              _) => true                          [owise]

    syntax Bool ::= #hasDynamicType(TypedArgs) [klabel(#hasDynamicType), function, total]
 // -------------------------------------------------------------------------------------
    rule #hasDynamicType(.TypedArgs) => false
    rule #hasDynamicType(T, TS) => #hasDynamicType(TS) requires #isStaticType(T)
    rule #hasDynamicType(T,  _) => true requires notBool #isStaticType(T)
```

`#sizeOfDynamicType` is used to calculate the size of a single dynamic `TypedArg`.
 - for `#bytes(BS)` and `#string(BS)`, the size is 32 bytes for the length prefix plus the size of the actual byte sequence, rounded up to the nearest multiple of 32.
 - for `#tuple(ARGS)`, the size is 32 bytes for the length prefix plus the cumulative size of its elements.
 - for `#array(T, N, _)` that has elements of a static `TypedArg` `T`, the size is `32 * (1 + N)`,which accounts for 32 bytes for the length prefix and 32 bytes for each element.
 - for dynamic type arrays `#array(T, N, ELEMS)`, the size is `32 * (1 + N + #sizeOfDynamicTypeList(ELEMS))`.

```k
    syntax Int ::= #sizeOfDynamicType ( TypedArg ) [klabel(#sizeOfDynamicType), function]
 // -------------------------------------------------------------------------------------
    rule #sizeOfDynamicType(     #bytes(BS)) => 32 +Int #ceil32(lengthBytes(BS))
    rule #sizeOfDynamicType(    #string(BS)) => 32 +Int #ceil32(lengthBytes(String2Bytes(BS)))
    rule #sizeOfDynamicType(   #tuple(ARGS)) => 32 +Int #sizeOfDynamicTypeList(ARGS)
    rule #sizeOfDynamicType(#array(T, N, _)) => 32 *Int (1 +Int N)
      requires #isStaticType(T)

    rule #sizeOfDynamicType(#array(T, N, ELEMS)) => (32 *Int (1 +Int N)) +Int #sizeOfDynamicTypeList(ELEMS)
      requires notBool #isStaticType(T)

    syntax Int ::= #sizeOfDynamicTypeList ( TypedArgs ) [klabel(#sizeOfDynamicTypeList), function, total]
 // -----------------------------------------------------------------------------------------------------
    rule #sizeOfDynamicTypeList(TARG, TARGS) => #sizeOfDynamicType(TARG) +Int #sizeOfDynamicTypeList(TARGS)
      requires notBool #isStaticType(TARG)

    rule #sizeOfDynamicTypeList(TARG, TARGS) => #lenOfHead(TARG) +Int #sizeOfDynamicTypeList(TARGS)
      requires #isStaticType(TARG)

    rule #sizeOfDynamicTypeList(.TypedArgs) => 0

    syntax Bytes ::= #enc ( TypedArg ) [klabel(#enc), function]
 // -----------------------------------------------------------
    // static Type
    rule #enc(#address( DATA )) => #bufStrict(32, #getValue(#address( DATA )))

    rule #enc(#uint256( DATA )) => #bufStrict(32, #getValue(#uint256( DATA )))
    rule #enc(#uint248( DATA )) => #bufStrict(32, #getValue(#uint248( DATA )))
    rule #enc(#uint240( DATA )) => #bufStrict(32, #getValue(#uint240( DATA )))
    rule #enc(#uint232( DATA )) => #bufStrict(32, #getValue(#uint232( DATA )))
    rule #enc(#uint224( DATA )) => #bufStrict(32, #getValue(#uint224( DATA )))
    rule #enc(#uint216( DATA )) => #bufStrict(32, #getValue(#uint216( DATA )))
    rule #enc(#uint208( DATA )) => #bufStrict(32, #getValue(#uint208( DATA )))
    rule #enc(#uint200( DATA )) => #bufStrict(32, #getValue(#uint200( DATA )))
    rule #enc(#uint192( DATA )) => #bufStrict(32, #getValue(#uint192( DATA )))
    rule #enc(#uint184( DATA )) => #bufStrict(32, #getValue(#uint184( DATA )))
    rule #enc(#uint176( DATA )) => #bufStrict(32, #getValue(#uint176( DATA )))
    rule #enc(#uint168( DATA )) => #bufStrict(32, #getValue(#uint168( DATA )))
    rule #enc(#uint160( DATA )) => #bufStrict(32, #getValue(#uint160( DATA )))
    rule #enc(#uint152( DATA )) => #bufStrict(32, #getValue(#uint152( DATA )))
    rule #enc(#uint144( DATA )) => #bufStrict(32, #getValue(#uint144( DATA )))
    rule #enc(#uint136( DATA )) => #bufStrict(32, #getValue(#uint136( DATA )))
    rule #enc(#uint128( DATA )) => #bufStrict(32, #getValue(#uint128( DATA )))
    rule #enc(#uint120( DATA )) => #bufStrict(32, #getValue(#uint120( DATA )))
    rule #enc(#uint112( DATA )) => #bufStrict(32, #getValue(#uint112( DATA )))
    rule #enc(#uint104( DATA )) => #bufStrict(32, #getValue(#uint104( DATA )))
    rule #enc( #uint96( DATA )) => #bufStrict(32, #getValue( #uint96( DATA )))
    rule #enc( #uint88( DATA )) => #bufStrict(32, #getValue( #uint88( DATA )))
    rule #enc( #uint80( DATA )) => #bufStrict(32, #getValue( #uint80( DATA )))
    rule #enc( #uint72( DATA )) => #bufStrict(32, #getValue( #uint72( DATA )))
    rule #enc( #uint64( DATA )) => #bufStrict(32, #getValue( #uint64( DATA )))
    rule #enc( #uint56( DATA )) => #bufStrict(32, #getValue( #uint56( DATA )))
    rule #enc( #uint48( DATA )) => #bufStrict(32, #getValue( #uint48( DATA )))
    rule #enc( #uint40( DATA )) => #bufStrict(32, #getValue( #uint40( DATA )))
    rule #enc( #uint32( DATA )) => #bufStrict(32, #getValue( #uint32( DATA )))
    rule #enc( #uint24( DATA )) => #bufStrict(32, #getValue( #uint24( DATA )))
    rule #enc( #uint16( DATA )) => #bufStrict(32, #getValue( #uint16( DATA )))
    rule #enc(  #uint8( DATA )) => #bufStrict(32, #getValue(  #uint8( DATA )))

    rule #enc(#int256( DATA )) => #bufStrict(32, #getValue(#int256( DATA )))
    rule #enc(#int248( DATA )) => #bufStrict(32, #getValue(#int248( DATA )))
    rule #enc(#int240( DATA )) => #bufStrict(32, #getValue(#int240( DATA )))
    rule #enc(#int232( DATA )) => #bufStrict(32, #getValue(#int232( DATA )))
    rule #enc(#int224( DATA )) => #bufStrict(32, #getValue(#int224( DATA )))
    rule #enc(#int216( DATA )) => #bufStrict(32, #getValue(#int216( DATA )))
    rule #enc(#int208( DATA )) => #bufStrict(32, #getValue(#int208( DATA )))
    rule #enc(#int200( DATA )) => #bufStrict(32, #getValue(#int200( DATA )))
    rule #enc(#int192( DATA )) => #bufStrict(32, #getValue(#int192( DATA )))
    rule #enc(#int184( DATA )) => #bufStrict(32, #getValue(#int184( DATA )))
    rule #enc(#int176( DATA )) => #bufStrict(32, #getValue(#int176( DATA )))
    rule #enc(#int168( DATA )) => #bufStrict(32, #getValue(#int168( DATA )))
    rule #enc(#int160( DATA )) => #bufStrict(32, #getValue(#int160( DATA )))
    rule #enc(#int152( DATA )) => #bufStrict(32, #getValue(#int152( DATA )))
    rule #enc(#int144( DATA )) => #bufStrict(32, #getValue(#int144( DATA )))
    rule #enc(#int136( DATA )) => #bufStrict(32, #getValue(#int136( DATA )))
    rule #enc(#int128( DATA )) => #bufStrict(32, #getValue(#int128( DATA )))
    rule #enc(#int120( DATA )) => #bufStrict(32, #getValue(#int120( DATA )))
    rule #enc(#int112( DATA )) => #bufStrict(32, #getValue(#int112( DATA )))
    rule #enc(#int104( DATA )) => #bufStrict(32, #getValue(#int104( DATA )))
    rule #enc( #int96( DATA )) => #bufStrict(32, #getValue( #int96( DATA )))
    rule #enc( #int88( DATA )) => #bufStrict(32, #getValue( #int88( DATA )))
    rule #enc( #int80( DATA )) => #bufStrict(32, #getValue( #int80( DATA )))
    rule #enc( #int72( DATA )) => #bufStrict(32, #getValue( #int72( DATA )))
    rule #enc( #int64( DATA )) => #bufStrict(32, #getValue( #int64( DATA )))
    rule #enc( #int56( DATA )) => #bufStrict(32, #getValue( #int56( DATA )))
    rule #enc( #int48( DATA )) => #bufStrict(32, #getValue( #int48( DATA )))
    rule #enc( #int40( DATA )) => #bufStrict(32, #getValue( #int40( DATA )))
    rule #enc( #int32( DATA )) => #bufStrict(32, #getValue( #int32( DATA )))
    rule #enc( #int24( DATA )) => #bufStrict(32, #getValue( #int24( DATA )))
    rule #enc( #int16( DATA )) => #bufStrict(32, #getValue( #int16( DATA )))
    rule #enc(  #int8( DATA )) => #bufStrict(32, #getValue(  #int8( DATA )))

    rule #enc(  #bytes1( DATA )) => #padRightToWidth(32, #bufStrict(1,  #getValue(#bytes1( DATA ))))
    rule #enc(  #bytes2( DATA )) => #padRightToWidth(32, #bufStrict(2,  #getValue(#bytes2( DATA ))))
    rule #enc(  #bytes3( DATA )) => #padRightToWidth(32, #bufStrict(3,  #getValue(#bytes3( DATA ))))
    rule #enc(  #bytes4( DATA )) => #padRightToWidth(32, #bufStrict(4,  #getValue(#bytes4( DATA ))))
    rule #enc(  #bytes5( DATA )) => #padRightToWidth(32, #bufStrict(5,  #getValue(#bytes5( DATA ))))
    rule #enc(  #bytes6( DATA )) => #padRightToWidth(32, #bufStrict(6,  #getValue(#bytes6( DATA ))))
    rule #enc(  #bytes7( DATA )) => #padRightToWidth(32, #bufStrict(7,  #getValue(#bytes7( DATA ))))
    rule #enc(  #bytes8( DATA )) => #padRightToWidth(32, #bufStrict(8,  #getValue(#bytes8( DATA ))))
    rule #enc(  #bytes9( DATA )) => #padRightToWidth(32, #bufStrict(9,  #getValue(#bytes9( DATA ))))
    rule #enc( #bytes10( DATA )) => #padRightToWidth(32, #bufStrict(10, #getValue(#bytes10( DATA ))))
    rule #enc( #bytes11( DATA )) => #padRightToWidth(32, #bufStrict(11, #getValue(#bytes11( DATA ))))
    rule #enc( #bytes12( DATA )) => #padRightToWidth(32, #bufStrict(12, #getValue(#bytes12( DATA ))))
    rule #enc( #bytes13( DATA )) => #padRightToWidth(32, #bufStrict(13, #getValue(#bytes13( DATA ))))
    rule #enc( #bytes14( DATA )) => #padRightToWidth(32, #bufStrict(14, #getValue(#bytes14( DATA ))))
    rule #enc( #bytes15( DATA )) => #padRightToWidth(32, #bufStrict(15, #getValue(#bytes15( DATA ))))
    rule #enc( #bytes16( DATA )) => #padRightToWidth(32, #bufStrict(16, #getValue(#bytes16( DATA ))))
    rule #enc( #bytes17( DATA )) => #padRightToWidth(32, #bufStrict(17, #getValue(#bytes17( DATA ))))
    rule #enc( #bytes18( DATA )) => #padRightToWidth(32, #bufStrict(18, #getValue(#bytes18( DATA ))))
    rule #enc( #bytes19( DATA )) => #padRightToWidth(32, #bufStrict(19, #getValue(#bytes19( DATA ))))
    rule #enc( #bytes20( DATA )) => #padRightToWidth(32, #bufStrict(20, #getValue(#bytes20( DATA ))))
    rule #enc( #bytes21( DATA )) => #padRightToWidth(32, #bufStrict(21, #getValue(#bytes21( DATA ))))
    rule #enc( #bytes22( DATA )) => #padRightToWidth(32, #bufStrict(22, #getValue(#bytes22( DATA ))))
    rule #enc( #bytes23( DATA )) => #padRightToWidth(32, #bufStrict(23, #getValue(#bytes23( DATA ))))
    rule #enc( #bytes24( DATA )) => #padRightToWidth(32, #bufStrict(24, #getValue(#bytes24( DATA ))))
    rule #enc( #bytes25( DATA )) => #padRightToWidth(32, #bufStrict(25, #getValue(#bytes25( DATA ))))
    rule #enc( #bytes26( DATA )) => #padRightToWidth(32, #bufStrict(26, #getValue(#bytes26( DATA ))))
    rule #enc( #bytes27( DATA )) => #padRightToWidth(32, #bufStrict(27, #getValue(#bytes27( DATA ))))
    rule #enc( #bytes28( DATA )) => #padRightToWidth(32, #bufStrict(28, #getValue(#bytes28( DATA ))))
    rule #enc( #bytes29( DATA )) => #padRightToWidth(32, #bufStrict(29, #getValue(#bytes29( DATA ))))
    rule #enc( #bytes30( DATA )) => #padRightToWidth(32, #bufStrict(30, #getValue(#bytes30( DATA ))))
    rule #enc( #bytes31( DATA )) => #padRightToWidth(32, #bufStrict(31, #getValue(#bytes31( DATA ))))
    rule #enc( #bytes32( DATA )) => #bufStrict(32, #getValue(#bytes32( DATA )))

    rule #enc(   #bool( DATA )) => #bufStrict(32, #getValue(   #bool( DATA )))

    // dynamic Type
    // length of `bytes` variables is hardcoded to be <= 1 Gb; this can be adjusted to reflect real-world on-chain constraints
    rule #enc(        #bytes(BS)) => #encBytes(lengthBytes(BS), BS) ensures lengthBytes(BS) <=Int 1073741824
    rule #enc(      #string(STR)) => #enc(#bytes(String2Bytes(STR)))
    rule #enc(#array(_, N, DATA)) => #enc(#uint256(N)) +Bytes #encodeArgs(DATA)
    rule #enc(    #tuple( DATA )) => #encodeArgs(DATA)

    syntax Bytes ::= #encBytes ( Int , Bytes ) [klabel(#encBytes), function]
 // ------------------------------------------------------------------------
    rule #encBytes(N, BS) => #enc(#uint256(N)) +Bytes BS +Bytes #bufStrict(#ceil32(N) -Int N, 0)
```

```k
    syntax Int ::= #getValue ( TypedArg ) [klabel(#getValue), function]
 // -------------------------------------------------------------------
    rule #getValue(   #bool( X )) => X       requires #rangeBool(X)

    rule #getValue(#address( X )) => X       requires #rangeAddress(X)

    rule #getValue(  #uint8( X )) => X       requires #rangeUInt(8,   X)
    rule #getValue( #uint16( X )) => X       requires #rangeUInt(16,  X)
    rule #getValue( #uint24( X )) => X       requires #rangeUInt(24,  X)
    rule #getValue( #uint32( X )) => X       requires #rangeUInt(32,  X)
    rule #getValue( #uint40( X )) => X       requires #rangeUInt(40,  X)
    rule #getValue( #uint48( X )) => X       requires #rangeUInt(48,  X)
    rule #getValue( #uint56( X )) => X       requires #rangeUInt(56,  X)
    rule #getValue( #uint64( X )) => X       requires #rangeUInt(64,  X)
    rule #getValue( #uint72( X )) => X       requires #rangeUInt(72,  X)
    rule #getValue( #uint80( X )) => X       requires #rangeUInt(80,  X)
    rule #getValue( #uint88( X )) => X       requires #rangeUInt(88,  X)
    rule #getValue( #uint96( X )) => X       requires #rangeUInt(96,  X)
    rule #getValue(#uint104( X )) => X       requires #rangeUInt(104, X)
    rule #getValue(#uint112( X )) => X       requires #rangeUInt(112, X)
    rule #getValue(#uint120( X )) => X       requires #rangeUInt(120, X)
    rule #getValue(#uint128( X )) => X       requires #rangeUInt(128, X)
    rule #getValue(#uint136( X )) => X       requires #rangeUInt(136, X)
    rule #getValue(#uint144( X )) => X       requires #rangeUInt(144, X)
    rule #getValue(#uint152( X )) => X       requires #rangeUInt(152, X)
    rule #getValue(#uint160( X )) => X       requires #rangeUInt(160, X)
    rule #getValue(#uint168( X )) => X       requires #rangeUInt(168, X)
    rule #getValue(#uint176( X )) => X       requires #rangeUInt(176, X)
    rule #getValue(#uint184( X )) => X       requires #rangeUInt(184, X)
    rule #getValue(#uint192( X )) => X       requires #rangeUInt(192, X)
    rule #getValue(#uint200( X )) => X       requires #rangeUInt(200, X)
    rule #getValue(#uint208( X )) => X       requires #rangeUInt(208, X)
    rule #getValue(#uint216( X )) => X       requires #rangeUInt(216, X)
    rule #getValue(#uint224( X )) => X       requires #rangeUInt(224, X)
    rule #getValue(#uint232( X )) => X       requires #rangeUInt(232, X)
    rule #getValue(#uint240( X )) => X       requires #rangeUInt(240, X)
    rule #getValue(#uint248( X )) => X       requires #rangeUInt(248, X)
    rule #getValue(#uint256( X )) => X       requires #rangeUInt(256, X)

    rule #getValue(   #int8( X )) => chop(X) requires #rangeSInt(8,   X)
    rule #getValue(  #int16( X )) => chop(X) requires #rangeSInt(16,  X)
    rule #getValue(  #int24( X )) => chop(X) requires #rangeSInt(24,  X)
    rule #getValue(  #int32( X )) => chop(X) requires #rangeSInt(32,  X)
    rule #getValue(  #int40( X )) => chop(X) requires #rangeSInt(40,  X)
    rule #getValue(  #int48( X )) => chop(X) requires #rangeSInt(48,  X)
    rule #getValue(  #int56( X )) => chop(X) requires #rangeSInt(56,  X)
    rule #getValue(  #int64( X )) => chop(X) requires #rangeSInt(64,  X)
    rule #getValue(  #int72( X )) => chop(X) requires #rangeSInt(72,  X)
    rule #getValue(  #int80( X )) => chop(X) requires #rangeSInt(80,  X)
    rule #getValue(  #int88( X )) => chop(X) requires #rangeSInt(88,  X)
    rule #getValue(  #int96( X )) => chop(X) requires #rangeSInt(96,  X)
    rule #getValue( #int104( X )) => chop(X) requires #rangeSInt(104, X)
    rule #getValue( #int112( X )) => chop(X) requires #rangeSInt(112, X)
    rule #getValue( #int120( X )) => chop(X) requires #rangeSInt(120, X)
    rule #getValue( #int128( X )) => chop(X) requires #rangeSInt(128, X)
    rule #getValue( #int136( X )) => chop(X) requires #rangeSInt(136, X)
    rule #getValue( #int144( X )) => chop(X) requires #rangeSInt(144, X)
    rule #getValue( #int152( X )) => chop(X) requires #rangeSInt(152, X)
    rule #getValue( #int160( X )) => chop(X) requires #rangeSInt(160, X)
    rule #getValue( #int168( X )) => chop(X) requires #rangeSInt(168, X)
    rule #getValue( #int176( X )) => chop(X) requires #rangeSInt(176, X)
    rule #getValue( #int184( X )) => chop(X) requires #rangeSInt(184, X)
    rule #getValue( #int192( X )) => chop(X) requires #rangeSInt(192, X)
    rule #getValue( #int200( X )) => chop(X) requires #rangeSInt(200, X)
    rule #getValue( #int208( X )) => chop(X) requires #rangeSInt(208, X)
    rule #getValue( #int216( X )) => chop(X) requires #rangeSInt(216, X)
    rule #getValue( #int224( X )) => chop(X) requires #rangeSInt(224, X)
    rule #getValue( #int232( X )) => chop(X) requires #rangeSInt(232, X)
    rule #getValue( #int240( X )) => chop(X) requires #rangeSInt(240, X)
    rule #getValue( #int248( X )) => chop(X) requires #rangeSInt(248, X)
    rule #getValue( #int256( X )) => chop(X) requires #rangeSInt(256, X)

    rule #getValue( #bytes1( X )) => X       requires #rangeUInt(8,   X)
    rule #getValue( #bytes2( X )) => X       requires #rangeUInt(16,  X)
    rule #getValue( #bytes3( X )) => X       requires #rangeUInt(24,  X)
    rule #getValue( #bytes4( X )) => X       requires #rangeUInt(32,  X)
    rule #getValue( #bytes5( X )) => X       requires #rangeUInt(40,  X)
    rule #getValue( #bytes6( X )) => X       requires #rangeUInt(48,  X)
    rule #getValue( #bytes7( X )) => X       requires #rangeUInt(56,  X)
    rule #getValue( #bytes8( X )) => X       requires #rangeUInt(64,  X)
    rule #getValue( #bytes9( X )) => X       requires #rangeUInt(72,  X)
    rule #getValue( #bytes10( X )) => X      requires #rangeUInt(80,  X)
    rule #getValue( #bytes11( X )) => X      requires #rangeUInt(88,  X)
    rule #getValue( #bytes12( X )) => X      requires #rangeUInt(96,  X)
    rule #getValue( #bytes13( X )) => X      requires #rangeUInt(104, X)
    rule #getValue( #bytes14( X )) => X      requires #rangeUInt(112, X)
    rule #getValue( #bytes15( X )) => X      requires #rangeUInt(120, X)
    rule #getValue( #bytes16( X )) => X      requires #rangeUInt(128, X)
    rule #getValue( #bytes17( X )) => X      requires #rangeUInt(136, X)
    rule #getValue( #bytes18( X )) => X      requires #rangeUInt(144, X)
    rule #getValue( #bytes19( X )) => X      requires #rangeUInt(152, X)
    rule #getValue( #bytes20( X )) => X      requires #rangeUInt(160, X)
    rule #getValue( #bytes21( X )) => X      requires #rangeUInt(168, X)
    rule #getValue( #bytes22( X )) => X      requires #rangeUInt(176, X)
    rule #getValue( #bytes23( X )) => X      requires #rangeUInt(184, X)
    rule #getValue( #bytes24( X )) => X      requires #rangeUInt(192, X)
    rule #getValue( #bytes25( X )) => X      requires #rangeUInt(200, X)
    rule #getValue( #bytes26( X )) => X      requires #rangeUInt(208, X)
    rule #getValue( #bytes27( X )) => X      requires #rangeUInt(216, X)
    rule #getValue( #bytes28( X )) => X      requires #rangeUInt(224, X)
    rule #getValue( #bytes29( X )) => X      requires #rangeUInt(232, X)
    rule #getValue( #bytes30( X )) => X      requires #rangeUInt(240, X)
    rule #getValue( #bytes31( X )) => X      requires #rangeUInt(248, X)
    rule #getValue( #bytes32( X )) => X      requires #rangeUInt(256, X)
```

### ABI Event Logs

EVM logs are special data structures in the blockchain, being searchable by off-chain clients.
Events are high-level wrappers of the EVM logs provided in the high-level languages.
Contracts can declare and generate the events, which will be compiled down to the EVM bytecode using the EVM log instructions.
The encoding scheme of the events in the EVM logs is defined in the Ethereum contract application binary interface (ABI) specification, leveraging the ABI call data encoding scheme.

The eDSL provides `#abiEventLog`, a notation to specify the EVM logs in the high-level events, defined below.
It specifies the contract account address, the event name, and the event arguments.
For example, the following notation represents an EVM log data that encodes the `Transfer` event generated by the `transfer` function, where `ACCT_ID` is the account address, and `CALLER_ID`, `TO_ID`, and `VALUE` are the event arguments.
Each argument is tagged with its ABI type (`#address` or `#uint256`), and the `indexed` attribute (`#indexed`) if any, according to the event declaration in the contract.

```
  #abiEventLog(ACCT_ID, "Transfer", #indexed(#address(CALLER_ID)), #indexed(#address(TO_ID)), #uint256(VALUE))
```

The above notation denotes (i.e., is translated to) the following EVM log data structure:

```
  { ACCT_ID                                                                                                                                                                                                                                                  | |`
  | 100389287136786176327247604509743168900146139575972864366142685224231313322991
  : CALLER_ID                                                                                                                                                                                                                                                |/|
  : TO_ID                                                                                                                                                                                                                                                    | |
  : .WordStack                                                                                                                                                                                                                                               | |
  | #bufStrict(32, VALUE)                                                                                                                                                                                                                           | |
  }
```

where `100389287136786176327247604509743168900146139575972864366142685224231313322991` is the hash value of the event signature, `keccak256("Transfer(address,address,unit256)")`.

```k
    syntax EventArg ::= TypedArg
                      | #indexed ( TypedArg ) [klabel(#indexed)]
 // ------------------------------------------------------------

    syntax EventArgs ::= List{EventArg, ","} [symbol(eventArgs)]
 // ------------------------------------------------------------

    syntax SubstateLogEntry ::= #abiEventLog ( Int , String , EventArgs ) [klabel(#abiEventLog), function]
 // ------------------------------------------------------------------------------------------------------
    rule #abiEventLog(ACCT_ID, EVENT_NAME, EVENT_ARGS)
      => { ACCT_ID | #getEventTopics(EVENT_NAME, EVENT_ARGS) | #encodeArgs(#getNonIndexedArgs(EVENT_ARGS)) }

    syntax List ::= #getEventTopics ( String , EventArgs ) [klabel(#getEventTopics), function]
 // ------------------------------------------------------------------------------------------
    rule #getEventTopics(ENAME, EARGS)
      => ListItem(#parseHexWord(Keccak256(String2Bytes(#generateSignature(ENAME, #getTypedArgs(EARGS))))))
         #getIndexedArgs(EARGS)

    syntax TypedArgs ::= #getTypedArgs ( EventArgs ) [klabel(#getTypedArgs), function]
 // ----------------------------------------------------------------------------------
    rule #getTypedArgs(#indexed(E), ES) => E, #getTypedArgs(ES)
    rule #getTypedArgs(E:TypedArg,  ES) => E, #getTypedArgs(ES)
    rule #getTypedArgs(.EventArgs)      => .TypedArgs

    syntax List ::= #getIndexedArgs ( EventArgs ) [klabel(#getIndexedArgs), function]
 // ---------------------------------------------------------------------------------
    rule #getIndexedArgs(#indexed(E), ES) => ListItem(#getValue(E)) #getIndexedArgs(ES)
    rule #getIndexedArgs(_:TypedArg,  ES) =>                        #getIndexedArgs(ES)
    rule #getIndexedArgs(.EventArgs)      => .List

    syntax TypedArgs ::= #getNonIndexedArgs ( EventArgs ) [klabel(#getNonIndexedArgs), function]
 // --------------------------------------------------------------------------------------------
    rule #getNonIndexedArgs(#indexed(_), ES) =>    #getNonIndexedArgs(ES)
    rule #getNonIndexedArgs(E:TypedArg,  ES) => E, #getNonIndexedArgs(ES)
    rule #getNonIndexedArgs(.EventArgs)      => .TypedArgs
```

### Function selectors

```k
    syntax Int ::= selector ( String ) [alias, klabel(abi_selector), symbol, function, no-evaluators]
 // -------------------------------------------------------------------------------------------------
```

```k
endmodule
```
