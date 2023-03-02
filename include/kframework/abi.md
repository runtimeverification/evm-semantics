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
                      | #int128  ( Int )                        [klabel(abi_type_int128),  symbol]
                      | #bytes4  ( Int )                        [klabel(abi_type_bytes4),  symbol]
                      | #bytes32 ( Int )                        [klabel(abi_type_bytes32), symbol]
                      | #bool    ( Int )                        [klabel(abi_type_bool),    symbol]
                      | #bytes   ( Bytes )                      [klabel(abi_type_bytes),   symbol]
                      | #string  ( String )                     [klabel(abi_type_string),  symbol]
                      | #array   ( TypedArg , Int , TypedArgs ) [klabel(abi_type_array),   symbol]
 // ----------------------------------------------------------------------------------------------

    syntax TypedArgs ::= List{TypedArg, ","} [klabel(typedArgs)]
 // ------------------------------------------------------------

    syntax Bytes ::= #abiCallData ( String , TypedArgs ) [function]
 // ---------------------------------------------------------------
    rule #abiCallData( FNAME , ARGS ) => #signatureCallData(FNAME, ARGS) +Bytes #encodeArgs(ARGS)

    syntax Bytes ::= #signatureCallData ( String, TypedArgs ) [function]
 // --------------------------------------------------------------------
    rule #signatureCallData( FNAME , ARGS ) => #parseByteStack(substrString(Keccak256(#generateSignature(FNAME, ARGS)), 0, 8))

    syntax String ::= #generateSignature     ( String, TypedArgs ) [function, total]
                    | #generateSignatureArgs ( TypedArgs )         [function, total]
 // --------------------------------------------------------------------------------
    rule #generateSignature( FNAME , ARGS ) => FNAME +String "(" +String #generateSignatureArgs(ARGS) +String ")"

    rule #generateSignatureArgs(.TypedArgs)                            => ""
    rule #generateSignatureArgs(TARGA:TypedArg, .TypedArgs)            => #typeName(TARGA)
    rule #generateSignatureArgs(TARGA:TypedArg, TARGB:TypedArg, TARGS) => #typeName(TARGA) +String "," +String #generateSignatureArgs(TARGB, TARGS)

    syntax String ::= #typeName ( TypedArg ) [function, total]
 // ----------------------------------------------------------
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
    rule #typeName(    #uint96( _ )) => "uint96"
    rule #typeName(    #uint88( _ )) => "uint88"
    rule #typeName(    #uint80( _ )) => "uint80"
    rule #typeName(    #uint72( _ )) => "uint72"
    rule #typeName(    #uint64( _ )) => "uint64"
    rule #typeName(    #uint56( _ )) => "uint56"
    rule #typeName(    #uint48( _ )) => "uint48"
    rule #typeName(    #uint40( _ )) => "uint40"
    rule #typeName(    #uint32( _ )) => "uint32"
    rule #typeName(    #uint24( _ )) => "uint24"
    rule #typeName(    #uint16( _ )) => "uint16"
    rule #typeName(     #uint8( _ )) => "uint8"

    rule #typeName(    #int256( _ )) => "int256"
    rule #typeName(    #int128( _ )) => "int128"

    rule #typeName(    #bytes4( _ )) => "bytes4"
    rule #typeName(   #bytes32( _ )) => "bytes32"

    rule #typeName(      #bool( _ )) => "bool"

    rule #typeName(     #bytes( _ )) => "bytes"

    rule #typeName(    #string( _ )) => "string"

    rule #typeName( #array(T, _, _)) => #typeName(T) +String "[]"

    syntax Bytes ::= #encodeArgs    ( TypedArgs )                       [function]
    syntax Bytes ::= #encodeArgsAux ( TypedArgs , Int , Bytes , Bytes ) [function]
 // ------------------------------------------------------------------------------
    rule #encodeArgs(ARGS) => #encodeArgsAux(ARGS, #lenOfHeads(ARGS), .Bytes, .Bytes)

    rule #encodeArgsAux(.TypedArgs, _:Int, HEADS, TAILS) => HEADS +Bytes TAILS

    rule #encodeArgsAux((ARG, ARGS), OFFSET, HEADS, TAILS)
        => #encodeArgsAux(ARGS, OFFSET, HEADS +Bytes #enc(ARG), TAILS)
      requires #isStaticType(ARG)

    rule #encodeArgsAux((ARG, ARGS), OFFSET, HEADS, TAILS)
        => #encodeArgsAux(ARGS, OFFSET +Int #sizeOfDynamicType(ARG), HEADS +Bytes #enc(#uint256(OFFSET)), TAILS +Bytes #enc(ARG))
      requires notBool(#isStaticType(ARG))

    syntax Int ::= #lenOfHeads ( TypedArgs ) [function, total]
 // ----------------------------------------------------------
    rule #lenOfHeads(.TypedArgs) => 0
    rule #lenOfHeads(ARG, ARGS)  => #lenOfHead(ARG) +Int #lenOfHeads(ARGS)

    syntax Int ::= #lenOfHead ( TypedArg ) [function, total]
 // --------------------------------------------------------
    rule #lenOfHead(  #address( _ )) => 32

    rule #lenOfHead(  #uint256( _ )) => 32
    rule #lenOfHead(  #uint248( _ )) => 32
    rule #lenOfHead(  #uint240( _ )) => 32
    rule #lenOfHead(  #uint232( _ )) => 32
    rule #lenOfHead(  #uint224( _ )) => 32
    rule #lenOfHead(  #uint216( _ )) => 32
    rule #lenOfHead(  #uint208( _ )) => 32
    rule #lenOfHead(  #uint200( _ )) => 32
    rule #lenOfHead(  #uint192( _ )) => 32
    rule #lenOfHead(  #uint184( _ )) => 32
    rule #lenOfHead(  #uint176( _ )) => 32
    rule #lenOfHead(  #uint168( _ )) => 32
    rule #lenOfHead(  #uint160( _ )) => 32
    rule #lenOfHead(  #uint152( _ )) => 32
    rule #lenOfHead(  #uint144( _ )) => 32
    rule #lenOfHead(  #uint136( _ )) => 32
    rule #lenOfHead(  #uint128( _ )) => 32
    rule #lenOfHead(  #uint120( _ )) => 32
    rule #lenOfHead(  #uint112( _ )) => 32
    rule #lenOfHead(  #uint104( _ )) => 32
    rule #lenOfHead(   #uint96( _ )) => 32
    rule #lenOfHead(   #uint88( _ )) => 32
    rule #lenOfHead(   #uint80( _ )) => 32
    rule #lenOfHead(   #uint72( _ )) => 32
    rule #lenOfHead(   #uint64( _ )) => 32
    rule #lenOfHead(   #uint56( _ )) => 32
    rule #lenOfHead(   #uint48( _ )) => 32
    rule #lenOfHead(   #uint40( _ )) => 32
    rule #lenOfHead(   #uint32( _ )) => 32
    rule #lenOfHead(   #uint24( _ )) => 32
    rule #lenOfHead(   #uint16( _ )) => 32
    rule #lenOfHead(    #uint8( _ )) => 32

    rule #lenOfHead(   #int256( _ )) => 32
    rule #lenOfHead(   #int128( _ )) => 32

    rule #lenOfHead(   #bytes4( _ )) => 32
    rule #lenOfHead(  #bytes32( _ )) => 32

    rule #lenOfHead(     #bool( _ )) => 32

    rule #lenOfHead(    #bytes( _ )) => 32

    rule #lenOfHead(   #string( _ )) => 32

    rule #lenOfHead(#array(_, _, _)) => 32

    syntax Bool ::= #isStaticType ( TypedArg ) [function, total]
 // ------------------------------------------------------------
    rule #isStaticType(  #address( _ )) => true

    rule #isStaticType(  #uint256( _ )) => true
    rule #isStaticType(  #uint248( _ )) => true
    rule #isStaticType(  #uint240( _ )) => true
    rule #isStaticType(  #uint232( _ )) => true
    rule #isStaticType(  #uint224( _ )) => true
    rule #isStaticType(  #uint216( _ )) => true
    rule #isStaticType(  #uint208( _ )) => true
    rule #isStaticType(  #uint200( _ )) => true
    rule #isStaticType(  #uint192( _ )) => true
    rule #isStaticType(  #uint184( _ )) => true
    rule #isStaticType(  #uint176( _ )) => true
    rule #isStaticType(  #uint168( _ )) => true
    rule #isStaticType(  #uint160( _ )) => true
    rule #isStaticType(  #uint152( _ )) => true
    rule #isStaticType(  #uint144( _ )) => true
    rule #isStaticType(  #uint136( _ )) => true
    rule #isStaticType(  #uint128( _ )) => true
    rule #isStaticType(  #uint120( _ )) => true
    rule #isStaticType(  #uint112( _ )) => true
    rule #isStaticType(  #uint104( _ )) => true
    rule #isStaticType(   #uint96( _ )) => true
    rule #isStaticType(   #uint88( _ )) => true
    rule #isStaticType(   #uint80( _ )) => true
    rule #isStaticType(   #uint72( _ )) => true
    rule #isStaticType(   #uint64( _ )) => true
    rule #isStaticType(   #uint56( _ )) => true
    rule #isStaticType(   #uint48( _ )) => true
    rule #isStaticType(   #uint40( _ )) => true
    rule #isStaticType(   #uint32( _ )) => true
    rule #isStaticType(   #uint24( _ )) => true
    rule #isStaticType(   #uint16( _ )) => true
    rule #isStaticType(    #uint8( _ )) => true

    rule #isStaticType(   #int256( _ )) => true
    rule #isStaticType(   #int128( _ )) => true

    rule #isStaticType(   #bytes4( _ )) => true
    rule #isStaticType(  #bytes32( _ )) => true

    rule #isStaticType(     #bool( _ )) => true

    rule #isStaticType(    #bytes( _ )) => false

    rule #isStaticType(   #string( _ )) => false

    rule #isStaticType(#array(_, _, _)) => false

    syntax Int ::= #sizeOfDynamicType ( TypedArg ) [function]
 // ---------------------------------------------------------
    rule #sizeOfDynamicType(#bytes(BS)) => 32 +Int #ceil32(lengthBytes(BS))

    rule #sizeOfDynamicType(#array(T, N, _)) => 32 *Int (1 +Int N)
      requires #isStaticType(T)

    rule #sizeOfDynamicType(#array(T, N, ELEMS)) => 32 *Int (1 +Int N +Int #sizeOfDynamicTypeAux(ELEMS))
      requires notBool #isStaticType(T)

    syntax Int ::= #sizeOfDynamicTypeAux ( TypedArgs ) [function]
 // -------------------------------------------------------------
    rule #sizeOfDynamicTypeAux(TARG, TARGS) => #sizeOfDynamicType(TARG) +Int #sizeOfDynamicTypeAux(TARGS)
      requires notBool #isStaticType(TARG)

    rule #sizeOfDynamicTypeAux(.TypedArgs) => 0

    syntax Bytes ::= #enc ( TypedArg ) [function]
 // ---------------------------------------------
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

    rule #enc( #int256( DATA )) => #bufStrict(32, #getValue( #int256( DATA )))
    rule #enc( #int128( DATA )) => #bufStrict(32, #getValue( #int128( DATA )))

    rule #enc( #bytes4( DATA )) => #padRightToWidth(32, #bufStrict(4, #getValue(#bytes4( DATA ))))
    rule #enc(#bytes32( DATA )) => #bufStrict(32, #getValue(#bytes32( DATA )))

    rule #enc(   #bool( DATA )) => #bufStrict(32, #getValue(   #bool( DATA )))

    // dynamic Type
    rule #enc(        #bytes(BS)) => #encBytes(lengthBytes(BS), BS)
    rule #enc(#array(_, N, DATA)) => #enc(#uint256(N)) +Bytes #encodeArgs(DATA)
    rule #enc(      #string(STR)) => #enc(#bytes(#parseByteStackRaw(STR)))

    syntax Bytes ::= #encBytes ( Int , Bytes ) [function]
 // -----------------------------------------------------
    rule #encBytes(N, BS) => #enc(#uint256(N)) +Bytes BS +Bytes #bufStrict(#ceil32(N) -Int N, 0)
```

```k
    syntax Int ::= #getValue ( TypedArg ) [function]
 // ------------------------------------------------
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

    rule #getValue( #int128( X )) => chop(X) requires #rangeSInt(128, X)
    rule #getValue( #int256( X )) => chop(X) requires #rangeSInt(256, X)

    rule #getValue( #bytes4( X )) => X       requires #rangeUInt(32,  X)
    rule #getValue(#bytes32( X )) => X       requires #rangeUInt(256, X)
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
                      | #indexed ( TypedArg )
 // -----------------------------------------

    syntax EventArgs ::= List{EventArg, ","} [klabel(eventArgs)]
 // ------------------------------------------------------------

    syntax SubstateLogEntry ::= #abiEventLog ( Int , String , EventArgs ) [function]
 // --------------------------------------------------------------------------------
    rule #abiEventLog(ACCT_ID, EVENT_NAME, EVENT_ARGS)
      => { ACCT_ID | #getEventTopics(EVENT_NAME, EVENT_ARGS) | #encodeArgs(#getNonIndexedArgs(EVENT_ARGS)) }

    syntax List ::= #getEventTopics ( String , EventArgs ) [function]
 // -----------------------------------------------------------------
    rule #getEventTopics(ENAME, EARGS)
      => ListItem(#parseHexWord(Keccak256(#generateSignature(ENAME, #getTypedArgs(EARGS)))))
         #getIndexedArgs(EARGS)

    syntax TypedArgs ::= #getTypedArgs ( EventArgs ) [function]
 // -----------------------------------------------------------
    rule #getTypedArgs(#indexed(E), ES) => E, #getTypedArgs(ES)
    rule #getTypedArgs(E:TypedArg,  ES) => E, #getTypedArgs(ES)
    rule #getTypedArgs(.EventArgs)      => .TypedArgs

    syntax List ::= #getIndexedArgs ( EventArgs ) [function]
 // --------------------------------------------------------
    rule #getIndexedArgs(#indexed(E), ES) => ListItem(#getValue(E)) #getIndexedArgs(ES)
    rule #getIndexedArgs(_:TypedArg,  ES) =>                        #getIndexedArgs(ES)
    rule #getIndexedArgs(.EventArgs)      => .List

    syntax TypedArgs ::= #getNonIndexedArgs ( EventArgs ) [function]
 // ----------------------------------------------------------------
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
