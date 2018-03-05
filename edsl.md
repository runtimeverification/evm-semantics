eDSL High-Level Notations
=========================

The eDSL high-level notations make the EVM specifications more succinct and closer to their high-level specifications.
The succinctness increases the readability, and the closeness helps "eye-ball validation" of the specification refinement.
The high-level notations are defined by translation to the corresponding EVM terms, and thus can be freely used with other EVM terms.
The notations are inspired by the production compilers of the smart contract languages like Solidity and Viper, and their definition is derived by formalizing the corresponding translation made by the compilers.

```k
module EDSL
    imports EVM
```

Reasoning Simplifications
-------------------------

We design abstractions that capture the EVM low-level specific details, allowing to specify specifications and reason about properties in a higher level similar to that of the surface languages (e.g., Solidity or Viper) in which smart contracts are written.

### Abstraction for Hash

We do not model the hash function as an injective function simply because it is not true due to the pigeonhole principle.
Instead, we abstract it as an uninterpreted function that captures the possibility of the hash collision, even if the probability is very small.

However, one can avoid reasoning about the potential collision by assuming all of the hashed values appearing in each execution trace are collision-free.
This can be achieved by instantiating the injectivity property only for the terms appearing in the symbolic execution, in a way analogous to the universal quantifier instantiation.
Hashed locations are essential for the storage layout schemes used to store compound data structures such as maps in the storage.

The following syntactic sugars capture the storage layout schemes of Solidity and Viper.

```k
    syntax IntList ::= List{Int, ""}                             [klabel(intList)]
    syntax Int     ::= #hashedLocation( String , Int , IntList ) [function]
 // -----------------------------------------------------------------------
    rule #hashedLocation(LANG, BASE, .IntList) => BASE

    rule #hashedLocation("Viper",    BASE, OFFSET OFFSETS) => #hashedLocation("Viper",    keccakIntList(BASE) +Word OFFSET, OFFSETS)
    rule #hashedLocation("Solidity", BASE, OFFSET OFFSETS) => #hashedLocation("Solidity", keccakIntList(OFFSET BASE),       OFFSETS)

    syntax Int ::= keccakIntList( IntList ) [function]
 // --------------------------------------------------
    rule keccakIntList(VS) => keccak(intList2ByteStack(VS))

    syntax WordStack ::= intList2ByteStack( IntList ) [function]
 // ------------------------------------------------------------
    rule intList2ByteStack(.IntList) => .WordStack
    rule intList2ByteStack(V VS)     => #padToWidth(32, #asByteStack(V)) ++ intList2ByteStack(VS)
      requires 0 <=Int V andBool V <Int pow256
```

ABI Abstraction DSL
-------------------

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

where `F1 : F2 : F3 : F4` is the (two's complement) byte-array representation of `2835717307`, the hash value of the `transfer` function signature ABI encoding, `keccak256("transfer(address,unit256)")`, and `T1 : ... : T32` and `V1 : ... : V32` are the byte-array representations of `TO` and `VALUE` respectively.

```k
    syntax TypedArg ::= #uint160 ( Int )
                      | #address ( Int )
                      | #uint256 ( Int )
 // ------------------------------------

    syntax TypedArgs ::= List{TypedArg, ","} [klabel(typedArgs)]
 // ------------------------------------------------------------

    syntax WordStack ::= #abiCallData ( String , TypedArgs ) [function]
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
    rule #typeName(#uint160( _ )) => "uint160"
    rule #typeName(#address( _ )) => "address"
    rule #typeName(#uint256( _ )) => "uint256"

    syntax WordStack ::= #encodeArgs ( TypedArgs ) [function]
 // ---------------------------------------------------------
    rule #encodeArgs(ARG, ARGS)  => #getData(ARG) ++ #encodeArgs(ARGS)
    rule #encodeArgs(.TypedArgs) => .WordStack

    syntax WordStack ::= #getData ( TypedArg ) [function]
 // -----------------------------------------------------
    rule #getData(#uint160( DATA )) => #padToWidth(32, #asByteStack(DATA))
    rule #getData(#address( DATA )) => #padToWidth(32, #asByteStack(DATA))
    rule #getData(#uint256( DATA )) => #padToWidth(32, #asByteStack(DATA))
```

### Event Logs

```k
    syntax EventArg ::= TypedArg
                      | #indexed ( TypedArg )
 // -----------------------------------------

    syntax EventArgs ::= List{EventArg, ","} [klabel(eventArgs)]
 // ------------------------------------------------------------

    syntax SubstateLogEntry ::= #abiEventLog ( Int , String , EventArgs ) [function]
 // --------------------------------------------------------------------------------
    rule #abiEventLog(ACCT_ID, EVENT_NAME, EVENT_ARGS)
      => { ACCT_ID | #getEventTopics(EVENT_NAME, EVENT_ARGS) | #getEventData(EVENT_ARGS) }

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

    syntax WordStack ::= #getEventData ( EventArgs ) [function]
 // -----------------------------------------------------------
    rule #getEventData(#indexed(_), ES) =>                #getEventData(ES)
    rule #getEventData(E:TypedArg,  ES) => #getData(E) ++ #getEventData(ES)
    rule #getEventData(.EventArgs)      => .WordStack

    syntax Int ::= #getValue ( TypedArg ) [function]
 // ------------------------------------------------
    rule #getValue(#uint160(V)) => V
    rule #getValue(#address(V)) => V
    rule #getValue(#uint256(V)) => V
endmodule
```
