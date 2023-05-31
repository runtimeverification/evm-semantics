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

 // Lemmas
 // ---------------

    rule         X &Int 127 <Int 128 => true requires 0 <=Int X                   [simplification, smt-lemma]
    rule 0 <=Int X &Int 127          => true requires 0 <=Int X                   [simplification, smt-lemma]
 // rule         X &Int 127 <=Int X  => true requires 0 <=Int X                   [simplification, smt-lemma]
    rule         X &Int 127  <Int 32 => true requires 0 <=Int X andBool X <Int 32 [simplification, smt-lemma]

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
claim (chop(chop(chop(chop(chop(chop((#lookup(ACCT_STORAGE, 0) /Int 2 &Int 127) +Int 31) /Int 32 *Int 32) +Int 32) +Int 128) +Int 32) +Int 32))
       => (((#lookup(ACCT_STORAGE, 0) /Int 2 &Int 127) +Int 31) /Int 32 *Int 32 +Int 224)
```

```k
claim (#lookup(ACCT_STORAGE, 0) /Int 2 <Int 32)
       => (false)
 requires 32 <=Int #lookup(ACCT_STORAGE, 0) /Int 2 &Int 127
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

          <callStack> .List                                       </callStack>
          <program>   #binRuntime(ERC721)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC721)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   ERC721.name()            </callData>
          <k>          #execute => #halt ...    </k>
          <output>     .Bytes   => ?_           </output>
          <statusCode> _        => EVMC_SUCCESS </statusCode>

          <account>
            <acctID>  ACCTID       </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires NAME_KEY             ==Int #loc(ERC721._name)
        andBool NAME                 ==Int #lookup(ACCT_STORAGE, NAME_KEY)
        andBool NAME &Int 1          ==Int 0
        andBool NAME /Int 2 &Int 127  <Int 32
```

```k
    claim [name.short.revert]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                       </callStack>
          <program>   #binRuntime(ERC721)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC721)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Bytes     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   ERC721.name()           </callData>
          <k>          #execute => #halt ...   </k>
          <output>     .Bytes   => ?_          </output>
          <statusCode> _        => EVMC_REVERT </statusCode>

          <account>
            <acctID>  ACCTID       </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires NAME_KEY    ==Int #loc(ERC721._name)
        andBool NAME        ==Int #lookup(ACCT_STORAGE, NAME_KEY)
        andBool NAME &Int 1 ==Int 0
        andBool 32          <=Int NAME /Int 2 &Int 127
```

```k
endmodule
```
