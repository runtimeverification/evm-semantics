eDSL High-Level Notations
=========================

The eDSL high-level notations make the EVM specifications more succinct and closer to their high-level specifications.
The succinctness increases the readability, and the closeness helps "eye-ball validation" of the specification refinement.
The high-level notations are defined by translation to the corresponding EVM terms, and thus can be freely used with other EVM terms.
The notations are inspired by the production compilers of the smart contract languages like Solidity and Vyper, and their definition is derived by formalizing the corresponding translation made by the compilers.

```k
requires "evm.k"

module EDSL         [symbolic]
    imports EVM
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
    syntax TypedArg ::= #uint160 ( Int )
                      | #address ( Int )
                      | #uint256 ( Int )
                      | #uint48  ( Int )
                      | #uint16  ( Int )
                      | #uint8   ( Int )
                      | #int256  ( Int )
                      | #int128  ( Int )
                      | #bytes32 ( Int )
                      | #bool    ( Int )
                      | #bytes   ( ByteArray )
                      | #string  ( String )
                      | #array   ( TypedArg , Int , TypedArgs )
 // -----------------------------------------------------------

    syntax TypedArgs ::= List{TypedArg, ","} [klabel(typedArgs)]
 // ------------------------------------------------------------

    syntax ByteArray ::= #abiCallData ( String , TypedArgs ) [function]
 // -------------------------------------------------------------------
    rule #abiCallData( FNAME , ARGS )
      => #parseByteStack(substrString(Keccak256(#generateSignature(FNAME, ARGS)), 0, 8))
      ++ #encodeArgs(ARGS)

    syntax String ::= #generateSignature     ( String, TypedArgs ) [function]
                    | #generateSignatureArgs ( TypedArgs )         [function]
 // -------------------------------------------------------------------------
    rule #generateSignature( FNAME , ARGS ) => FNAME +String "(" +String #generateSignatureArgs(ARGS) +String ")"

    rule #generateSignatureArgs(.TypedArgs)                            => ""
    rule #generateSignatureArgs(TARGA:TypedArg, .TypedArgs)            => #typeName(TARGA)
    rule #generateSignatureArgs(TARGA:TypedArg, TARGB:TypedArg, TARGS) => #typeName(TARGA) +String "," +String #generateSignatureArgs(TARGB, TARGS)

    syntax String ::= #typeName ( TypedArg ) [function]
 // ---------------------------------------------------
    rule #typeName(   #uint160( _ )) => "uint160"
    rule #typeName(   #address( _ )) => "address"
    rule #typeName(   #uint256( _ )) => "uint256"
    rule #typeName(    #uint48( _ )) => "uint48"
    rule #typeName(    #uint16( _ )) => "uint16"
    rule #typeName(     #uint8( _ )) => "uint8"
    rule #typeName(    #int256( _ )) => "int256"
    rule #typeName(    #int128( _ )) => "int128"
    rule #typeName(   #bytes32( _ )) => "bytes32"
    rule #typeName(      #bool( _ )) => "bool"
    rule #typeName(     #bytes( _ )) => "bytes"
    rule #typeName(    #string( _ )) => "string"
    rule #typeName( #array(T, _, _)) => #typeName(T) +String "[]"

    syntax ByteArray ::= #encodeArgs    ( TypedArgs )                               [function]
    syntax ByteArray ::= #encodeArgsAux ( TypedArgs , Int , ByteArray , ByteArray ) [function]
 // ------------------------------------------------------------------------------------------
    rule #encodeArgs(ARGS) => #encodeArgsAux(ARGS, #lenOfHeads(ARGS), .ByteArray, .ByteArray)

    rule #encodeArgsAux(.TypedArgs, _:Int, HEADS, TAILS) => HEADS ++ TAILS

    rule #encodeArgsAux((ARG, ARGS), OFFSET, HEADS, TAILS)
        => #encodeArgsAux(ARGS, OFFSET, HEADS ++ #enc(ARG), TAILS)
      requires #isStaticType(ARG)

    rule #encodeArgsAux((ARG, ARGS), OFFSET, HEADS, TAILS)
        => #encodeArgsAux(ARGS, OFFSET +Int #sizeOfDynamicType(ARG), HEADS ++ #enc(#uint256(OFFSET)), TAILS ++ #enc(ARG))
      requires notBool(#isStaticType(ARG))

    syntax Int ::= #lenOfHeads ( TypedArgs ) [function]
 // ---------------------------------------------------
    rule #lenOfHeads(.TypedArgs) => 0
    rule #lenOfHeads(ARG, ARGS)  => #lenOfHead(ARG) +Int #lenOfHeads(ARGS)

    syntax Int ::= #lenOfHead ( TypedArg ) [function]
 // -------------------------------------------------
    rule #lenOfHead(  #uint160( _ )) => 32
    rule #lenOfHead(  #address( _ )) => 32
    rule #lenOfHead(  #uint256( _ )) => 32
    rule #lenOfHead(   #uint48( _ )) => 32
    rule #lenOfHead(   #uint16( _ )) => 32
    rule #lenOfHead(    #uint8( _ )) => 32
    rule #lenOfHead(   #int256( _ )) => 32
    rule #lenOfHead(   #int128( _ )) => 32
    rule #lenOfHead(  #bytes32( _ )) => 32
    rule #lenOfHead(     #bool( _ )) => 32
    rule #lenOfHead(    #bytes( _ )) => 32
    rule #lenOfHead(   #string( _ )) => 32
    rule #lenOfHead(#array(_, _, _)) => 32

    syntax Bool ::= #isStaticType ( TypedArg ) [function]
 // -----------------------------------------------------
    rule #isStaticType(  #uint160( _ )) => true
    rule #isStaticType(  #address( _ )) => true
    rule #isStaticType(  #uint256( _ )) => true
    rule #isStaticType(   #uint48( _ )) => true
    rule #isStaticType(   #uint16( _ )) => true
    rule #isStaticType(    #uint8( _ )) => true
    rule #isStaticType(   #int256( _ )) => true
    rule #isStaticType(   #int128( _ )) => true
    rule #isStaticType(  #bytes32( _ )) => true
    rule #isStaticType(     #bool( _ )) => true
    rule #isStaticType(    #bytes( _ )) => false
    rule #isStaticType(   #string( _ )) => false
    rule #isStaticType(#array(_, _, _)) => false

    syntax Int ::= #sizeOfDynamicType ( TypedArg ) [function]
 // ---------------------------------------------------------
    rule #sizeOfDynamicType(#bytes(BS)) => 32 +Int #ceil32(#sizeByteArray(BS))

    rule #sizeOfDynamicType(#array(T, N, _)) => 32 *Int (1 +Int N)
      requires #isStaticType(T)

    rule #sizeOfDynamicType(#array(T, N, ELEMS)) => 32 *Int (1 +Int N +Int #sizeOfDynamicTypeAux(ELEMS))
      requires notBool #isStaticType(T)

    syntax Int ::= #sizeOfDynamicTypeAux ( TypedArgs ) [function]
 // -------------------------------------------------------------
    rule #sizeOfDynamicTypeAux(TARG, TARGS) => #sizeOfDynamicType(TARG) +Int #sizeOfDynamicTypeAux(TARGS)
      requires notBool #isStaticType(TARG)

    rule #sizeOfDynamicTypeAux(.TypedArgs) => 0

    syntax ByteArray ::= #enc ( TypedArg ) [function]
 // -------------------------------------------------
    // static Type
    rule #enc(#uint160( DATA )) => #buf(32, #getValue(#uint160( DATA )))
    rule #enc(#address( DATA )) => #buf(32, #getValue(#address( DATA )))
    rule #enc(#uint256( DATA )) => #buf(32, #getValue(#uint256( DATA )))
    rule #enc( #uint48( DATA )) => #buf(32, #getValue( #uint48( DATA )))
    rule #enc( #uint16( DATA )) => #buf(32, #getValue( #uint16( DATA )))
    rule #enc(  #uint8( DATA )) => #buf(32, #getValue(  #uint8( DATA )))
    rule #enc( #int256( DATA )) => #buf(32, #getValue( #int256( DATA )))
    rule #enc( #int128( DATA )) => #buf(32, #getValue( #int128( DATA )))
    rule #enc(#bytes32( DATA )) => #buf(32, #getValue(#bytes32( DATA )))
    rule #enc(   #bool( DATA )) => #buf(32, #getValue(   #bool( DATA )))

    // dynamic Type
    rule #enc(        #bytes(BS)) => #encBytes(#sizeByteArray(BS), BS)
    rule #enc(#array(_, N, DATA)) => #enc(#uint256(N)) ++ #encodeArgs(DATA)
    rule #enc(      #string(STR)) => #enc(#bytes(#parseByteStackRaw(STR)))

    syntax ByteArray ::= #encBytes ( Int , ByteArray ) [function]
 // -------------------------------------------------------------
    rule #encBytes(N, BS) => #enc(#uint256(N)) ++ BS ++ #buf(#ceil32(N) -Int N, 0)

    //Byte array buffer. Lemmas defined in evm-data-symbolic.k
    // SIZE, DATA // left zero padding
    syntax ByteArray ::= #buf ( Int , Int ) [function, smtlib(buf)]
 // ---------------------------------------------------------------
    rule #buf(SIZE, DATA) => #padToWidth(SIZE, #asByteStack(DATA))
      requires #range(0 <= DATA < (2 ^Int (SIZE *Int 8)))
      [concrete]

    syntax ByteArray ::= #bufSeg ( ByteArray , Int , Int ) [function, smtlib(bufSeg)] // BUFFER, START, WIDTH
    syntax Int       ::= #bufElm ( ByteArray , Int )       [function] // BUFFER, INDEX

    syntax Int ::= #getValue ( TypedArg ) [function]
 // ------------------------------------------------
    rule #getValue(#uint160( DATA )) => DATA
      requires #rangeUInt(160, DATA)

    rule #getValue(#address( DATA )) => DATA
      requires #rangeAddress(DATA)

    rule #getValue(#uint256( DATA )) => DATA
      requires #rangeUInt(256, DATA)

    rule #getValue(  #uint48( DATA )) => DATA
      requires #rangeUInt(48, DATA)

    rule #getValue(  #uint16( DATA )) => DATA
      requires #rangeUInt(16, DATA)

    rule #getValue(  #uint8( DATA )) => DATA
      requires #rangeUInt(8, DATA)

    rule #getValue( #int256( DATA )) => #unsigned(DATA)
      requires #rangeSInt(256, DATA)

    rule #getValue( #int128( DATA )) => #unsigned(DATA)
      requires #rangeSInt(128, DATA)

    rule #getValue(#bytes32( DATA )) => DATA
      requires #rangeUInt(256, DATA)

    rule #getValue(   #bool( DATA )) => DATA
      requires #range(0 <= DATA <= 1)

    syntax Int ::= #ceil32 ( Int ) [function, smtlib(ceil32), smt-prelude]
 // -----------------------------------------
    rule [#ceil32]: #ceil32(N) => ((N +Int 31) /Int 32) *Int 32
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
  | #buf(32, VALUE)                                                                                                                                                                                                                           | |
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
    rule #getNonIndexedArgs(#indexed(E), ES) =>    #getNonIndexedArgs(ES)
    rule #getNonIndexedArgs(E:TypedArg,  ES) => E, #getNonIndexedArgs(ES)
    rule #getNonIndexedArgs(.EventArgs)      => .TypedArgs
```

### Hashed Location for Storage

The storage accommodates permanent data such as the `balances` map.
A map is laid out in the storage where the map entries are scattered over the entire storage space using the (256-bit) hash of each key to determine the location.
The detailed mechanism of calculating the location varies by compilers.
In Vyper, for example, `map[key1][key2]` is stored at the location:

```
  hash(hash(key1 ++ slot(map)) ++ key2)
```

where `slot(map)` is the position index of `map` in the program, and `++` is byte-array concatenation, while in Solidity, it is stored at:

```
  hash(key2 ++ hash(key1 ++ slot(map)))
```

The eDSL provides `#hashedLocation` that allows to uniformly specify the locations in a form parameterized by the underlying compilers.
For maps, the location of `map[key1][key2]` can be specified as follows, where `{COMPILER}` is a place-holder to be replaced by the name of the compiler.
Note that the keys are separated by the white spaces instead of commas.

```
  #hashedLocation({COMPILER}, slot(map), key1 key2)
```

This notation makes the specification independent of the underlying compilers, enabling it to be reused for differently compiled programs.

For dynamically sized arrays in Solidity, and both statically and dynamically sized arrays in Vyper, the length of the array is stored at:

```
  hash(slot(array))
```

and the element at index `i` is stored at:

```
  hash(slot(array)) + i
```

More information about how storage locations are defined in Solidity can be found [here](https://solidity.readthedocs.io/en/v0.5.11/miscellaneous.html#layout-of-state-variables-in-storage).

Specifically, `#hashedLocation` is defined as follows, capturing the storage layout schemes of Solidity and Vyper.

```k
    syntax IntList ::= List{Int, ""}                             [klabel(intList)]
    syntax Int     ::= #hashedLocation( String , Int , IntList ) [function]
 // -----------------------------------------------------------------------
    rule #hashedLocation(LANG, BASE, .IntList) => BASE

    rule #hashedLocation("Vyper",    BASE, OFFSET OFFSETS) => #hashedLocation("Vyper",    keccakIntList(BASE OFFSET),       OFFSETS)
    rule #hashedLocation("Solidity", BASE, OFFSET OFFSETS) => #hashedLocation("Solidity", keccakIntList(OFFSET BASE),       OFFSETS)
    rule #hashedLocation("Array",    BASE, OFFSET OFFSETS) => #hashedLocation("Array",    keccakIntList(BASE) +Word OFFSET, OFFSETS)

    syntax Int ::= keccakIntList( IntList ) [function]
 // --------------------------------------------------
    rule [keccakIntList]: keccakIntList(VS) => keccak(intList2ByteArray(VS))

    syntax ByteArray ::= intList2ByteArray( IntList ) [function]
 // ------------------------------------------------------------
    rule intList2ByteArray(.IntList) => .ByteArray
    rule intList2ByteArray(V VS)     => #buf(32, V) ++ intList2ByteArray(VS)
      requires 0 <=Int V andBool V <Int pow256

    syntax IntList ::= byteStack2IntList ( ByteArray )       [function]
                     | byteStack2IntList ( ByteArray , Int ) [function]
 // -------------------------------------------------------------------
    rule byteStack2IntList ( WS ) => byteStack2IntList ( WS , #sizeByteArray(WS) /Int 32 )

    // #sizeWordStack(WS) is not necessarily a multiple of 32.
    rule byteStack2IntList ( WS , N )
         => #asWord ( WS [ 0 .. bytesInNextInt(WS, N) ] ) byteStack2IntList ( #drop(bytesInNextInt(WS, N), WS) , N -Int 1 )
         requires N >Int 0

    rule byteStack2IntList ( WS , 0 ) => .IntList

    syntax Int ::= bytesInNextInt ( ByteArray , Int ) [function]
 // ------------------------------------------------------------
    rule bytesInNextInt(WS, N) => #sizeByteArray(WS) -Int 32 *Int (N -Int 1)
```

Solidity stores values of type `bytes` and `string` in one slot if they are short enough.
If the data is at most 31 bytes long, it is stored in the higher-order bytes (left aligned) and the lowest-order byte stores `2 * length`.

```k
    syntax Int ::= #packBytes ( ByteArray ) [function]
 // --------------------------------------------------
    rule #packBytes( WS ) => #asInteger(#padRightToWidth(31, WS) ++ #asByteStack(2 *Int #sizeByteArray(WS)))
      requires #sizeByteArray(WS) <=Int 31
```

```k
endmodule
```
