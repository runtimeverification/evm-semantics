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
    imports LEMMAS-WITHOUT-SLOT-UPDATES
    imports EVM-OPTIMIZATIONS
    imports STORAGE-VERIFICATION

    syntax Step ::= Bytes | Int
    syntax KItem ::= runLemma ( Step ) [symbol(runLemma)] | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

 // decimals lemmas
 // ---------------

    rule         255 &Int X <Int 256 => true requires 0 <=Int X [simplification, smt-lemma]
    rule 0 <=Int 255 &Int X          => true requires 0 <=Int X [simplification, smt-lemma]

    rule bool2Word ( notBool WORD ==Int 0 ) => WORD           [simplification]

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
    claim <k> runLemma(#bufStrict(32, #loc(S2KStorage . myBool))) => doneLemma(#buf(32,0)) ... </k>
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
          <useGas>  true     </useGas>

          <callStack> .List                                        </callStack>
          <program>   #binRuntime(S2KStorage)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(S2KStorage)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <codeAddr>         ACCTID      => ?_ </codeAddr>
          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   S2KStorage.S2KmyBool()               </callData>
          <k>          #execute => #halt ...          </k>
          <output>     .Bytes   => #buf(32, MYBOOL)   </output>
          <statusCode> _        => EVMC_SUCCESS       </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires MYBOOL_KEY ==Int #loc(S2KStorage . myBool)
        andBool MYBOOL     ==Int 255 &Int #lookup(ACCT_STORAGE, MYBOOL_KEY)
```


```k
    claim [setMyBool]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>
          <useGas>  true     </useGas>

          <callStack> .List                                        </callStack>
          <program>   #binRuntime(S2KStorage)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(S2KStorage)) </jumpDests>
          <static>    false                                        </static>

          <id>         ACCTID      => ?_ </id>
          <codeAddr>         ACCTID      => ?_ </codeAddr>
          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   S2KStorage.S2KsetMyBool(NEW_VAL : bool) </callData>
          <k>          #execute   => #halt ...           </k>
          <output>     .Bytes                            </output>
          <statusCode> _          => EVMC_SUCCESS        </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE => ACCT_STORAGE [ MYBOOL_KEY <- NEW_STORAGE_CONTENT ] </storage>
            ...
          </account>

          <refund> _ => ?_ </refund>

       requires #rangeBool(NEW_VAL)
        andBool MYBOOL_KEY          ==Int #loc(S2KStorage . myBool)
        andBool OLD_STORAGE_CONTENT ==Int #lookup ( ACCT_STORAGE , MYBOOL_KEY )
        andBool NEW_STORAGE_CONTENT ==Int NEW_VAL |Int ((~Word 255) &Int OLD_STORAGE_CONTENT)

```

```k
endmodule
```
