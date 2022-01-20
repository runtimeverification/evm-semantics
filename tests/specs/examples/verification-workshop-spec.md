Verification Workshop
=====================

```k
requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
requires "lemmas/infinite-gas.k"
```

Solidity Code
-------------

File [`verification-workshop.sol`](verification-workshop.sol) contains some code snippets we want to verify the functional correctness of.
Call `kevm solc-to-k verification-workshop.sol MyContract > verification-workshop-bin-runtime.k`, to generate the helper K files.

Verification Module
-------------------

Helper module for verification tasks.

-   Add any lemmas needed for our proofs.
-   Import a large body of existing lemmas from KEVM.

```k
requires "verification-workshop-bin-runtime.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports INFINITE-GAS
    imports EVM-OPTIMIZATIONS
    imports MYCONTRACT-BIN-RUNTIME

    syntax Step ::= ByteArray | Int
 // -------------------------------

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

endmodule
```

K Specifications
----------------

Formal specifications (using KEVM) of the correctness properties for our Solidity code.

```k
module VERIFICATION-WORKSHOP-SPEC
    imports VERIFICATION
```

### Functional Lemmas

```k
```

### Getter/Setter

```k
    claim [getx]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                           </callStack>
          <program>   #binRuntime(MyContract)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(MyContract)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <static>     STATIC      => ?_ </static>
          <refund>     _           => ?_ </refund>

          <callData>   MyContract.getX() ++ _CD                                    </callData>
          <k>          #execute   => #halt ...                                     </k>
          <output>     .ByteArray => #buf(32, #lookup(ACCT_STORAGE, MyContract.x)) </output>
          <statusCode> _          => EVMC_SUCCESS                                  </statusCode>
          <account>
            <acctID>  ACCTID       </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>
```

```k
    claim [setx]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                           </callStack>
          <program>   #binRuntime(MyContract)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(MyContract)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <static>     STATIC      => ?_ </static>
          <refund>     _           => ?_ </refund>

          <callData>   MyContract.setX(X) ++ _CD  </callData>
          <k>          #execute   => #halt ...    </k>
          <output>     .ByteArray => ?_           </output>
          <statusCode> _          => EVMC_SUCCESS </statusCode>
          <account>
            <acctID>  ACCTID       </acctID>
            <storage> ACCT_STORAGE
                   => ACCT_STORAGE [ MyContract.x <- X ]
            </storage>
            ...
          </account>
       requires notBool STATIC
```

```k
    claim [max]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                           </callStack>
          <program>   #binRuntime(MyContract)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(MyContract)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <static>     STATIC      => ?_ </static>
          <refund>     _           => ?_ </refund>

          <callData>   MyContract.max(X, Y) ++ _CD                              </callData>
          <k>          #execute   => #halt ...                                  </k>
          <output>     .ByteArray => #buf(32, #if X <Int Y #then Y #else X #fi) </output>
          <statusCode> _          => EVMC_SUCCESS                               </statusCode>
          <account>
            <acctID>  ACCTID       </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>
```

```k
endmodule
```
