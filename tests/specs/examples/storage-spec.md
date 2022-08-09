Storage Verification
====================

```k
requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
```

Solidity Code
-------------

File [`Storage.sol`](Storage.sol) contains some code snippets we want to verify the functional correctness of.
Call `kevm solc-to-k Storage.sol Storage > storage-bin-runtime.k`, to generate the helper K files.

Verification Module
-------------------

Helper module for verification tasks.

-   Add any lemmas needed for our proofs.
-   Import a large body of existing lemmas from KEVM.

```k
requires "storage-bin-runtime.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports EVM-OPTIMIZATIONS
    imports STORAGE-VERIFICATION

    syntax Step ::= ByteArray | Int
    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

 // decimals lemmas
 // ---------------

    rule         255 &Int X <Int 256 => true requires 0 <=Int X [simplification, smt-lemma]
    rule 0 <=Int 255 &Int X          => true requires 0 <=Int X [simplification, smt-lemma]

endmodule
```

K Specifications
----------------

Formal specifications (using KEVM) of the correctness properties for our Solidity code.

```k
module STORAGE-SPEC
    imports VERIFICATION
```

### Functional Claims

```k
    claim <k> runLemma(#bufStrict(32, #loc(Storage.myBool))) => doneLemma(#buf(32, keccak(#buf(32, OWNER) ++ #buf(32, 1)))) ... </k>
```

### Calling myBool() works

-   Everything from `<mode>` to `<callValue>` is boilerplate.
-   We are setting `<callData>` to `myBool()`.
-   We ask the prover to show that in all cases, we will end in `EVMC_SUCCESS` (rollback) when this happens.
-   The `<output>` cell specifies that we correctly lookup the `myBool` value from the account storage.

```k
    claim [myBool]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                        </callStack>
          <program>   #binRuntime(Storage)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(Storage)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   Storage.myBool()                 </callData>
          <k>          #execute   => #halt ...          </k>
          <output>     .ByteArray => #buf(32, MYBOOL)   </output>
          <statusCode> _          => EVMC_SUCCESS       </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires MYBOOL_KEY ==Int #loc(Storage.myBool)
        andBool MYBOOL     ==Int 255 &Int #lookup(ACCT_STORAGE, MYBOOL)
```

```k
endmodule
```
