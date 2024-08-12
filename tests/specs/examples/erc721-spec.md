ERC721-ish Verification
=======================

```k
requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
```

Solidity Code
-------------

File [`ERC721.sol`](ERC721.sol) contains some code snippets we want to verify the functional correctness of.
Call `kevm solc-to-k ERC721.sol ERC721 > erc721-bin-runtime.k`, to generate the helper K files.

Verification Module
-------------------

Helper module for verification tasks.

-   Add any lemmas needed for our proofs.
-   Import a large body of existing lemmas from KEVM.

```k
requires "erc721-bin-runtime.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports EVM-OPTIMIZATIONS
    imports ERC721-VERIFICATION

    syntax Step ::= Bytes | Int | Bool
    syntax KItem ::= runLemma ( Step ) [symbol(runLemma)] | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

 // Lemmas
 // ---------------

    rule         127 &Int X <Int 128 => true requires 0 <=Int X                   [simplification, smt-lemma]
    rule 0 <=Int 127 &Int X          => true requires 0 <=Int X                   [simplification, smt-lemma]
 // rule         127 &Int X <=Int X  => true requires 0 <=Int X                   [simplification, smt-lemma]
    rule         127 &Int    <Int 32 => true requires 0 <=Int X andBool X <Int 32 [simplification, smt-lemma]

    rule chop(X +Int Y) => X +Int Y requires 0 <=Int X andBool #rangeUInt(256, Y) andBool X <=Int maxUInt256 -Int Y [simplification, concrete(Y)]
    rule 32 *Int ((X +Int 31) /Int 32) <=Int Y => 0 <=Int X andBool X <=Int Y -Int 31 [simplification, concrete(Y)]
    rule 127 &Int X <=Int Y => true requires 0 <=Int X andBool 127 <=Int Y [simplification, concrete(Y)]

endmodule
```

K Specifications
----------------

Formal specifications (using KEVM) of the correctness properties for our Solidity code.

```k
module ERC721-SPEC
    imports VERIFICATION
```

```k
claim [lemma.1]:
      <k> runLemma(chop(chop(chop(chop(chop(chop((127 &Int (#lookup(ACCT_STORAGE, 0) /Int 2)) +Int 31) /Int 32 *Int 32) +Int 32) +Int 128) +Int 32) +Int 32))
       => doneLemma(((127 &Int (#lookup(ACCT_STORAGE, 0) /Int 2)) +Int 31) /Int 32 *Int 32 +Int 224) ... </k>
```

```k
claim [lemma.2]:
      <k> runLemma(#lookup(ACCT_STORAGE, 0) /Int 2 <Int 32)
       => doneLemma(false) ... </k>
 requires 32 <=Int 127 &Int ( #lookup(ACCT_STORAGE, 0) /Int 2 )
```

```k
claim [lemma.3]:
      <k> runLemma(chop((((((127 &Int (#lookup(ACCT_STORAGE:Map, 0) /Int 2)) +Int 31) /Int 32) *Int 32) +Int 224)))
       => doneLemma((((((127 &Int (#lookup(ACCT_STORAGE:Map, 0) /Int 2)) +Int 31) /Int 32) *Int 32) +Int 224)) ... </k>
```

### Calling name() works

-   Everything from `<mode>` to `<callValue>` is boilerplate.
-   We are setting `<callData>` to `name()`.
-   We claim that if NAME is a short string, we will end in `EVMC_SUCCESS` if it is well-formed, and in `EVMC_REVERT` otherwise.
-   TODO: Add claims for long strings.
-   TODO: The `<output>` cell specifies that we correctly lookup the `NAME` value from the account storage.

```k
    claim [name.short.success]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>
          <useGas>  true     </useGas>

          <callStack> .List                                       </callStack>
          <program>   #binRuntime(S2KERC721)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(S2KERC721)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   S2KERC721.S2Kname()      </callData>
          <k>          #execute => #halt ...    </k>
          <output>     .Bytes   => ?_           </output>
          <statusCode> _        => EVMC_SUCCESS </statusCode>

          <account>
            <acctID>  ACCTID       </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires NAME_KEY             ==Int #loc(S2KERC721._name)
        andBool NAME                 ==Int #lookup(ACCT_STORAGE, NAME_KEY)
        andBool 1 &Int NAME          ==Int 0
        andBool 127 &Int (NAME /Int)  <Int 32
```

**TODO**: This proof isn't passing.

```
    claim [name.short.revert]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>
          <useGas>  true     </useGas>

          <callStack> .List                                       </callStack>
          <program>   #binRuntime(S2KERC721)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(S2KERC721)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   S2KERC721.S2Kname()     </callData>
          <k>          #execute => #halt ...   </k>
          <output>     .Bytes   => ?_          </output>
          <statusCode> _        => EVMC_REVERT </statusCode>

          <account>
            <acctID>  ACCTID       </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires NAME_KEY    ==Int #loc(S2KERC721._name)
        andBool NAME        ==Int #lookup(ACCT_STORAGE, NAME_KEY)
        andBool 1 &Int NAME ==Int 0
        andBool 32          <=Int 127 &Int (NAME /Int 2)
```

```k
endmodule
```
