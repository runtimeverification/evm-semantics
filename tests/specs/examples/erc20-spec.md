ERC20-ish Verification
======================

```k
requires "edsl.md"
requires "optimizations.md"
requires "lemmas/lemmas.k"
requires "lemmas/infinite-gas.k"
```

Solidity Code
-------------

File [`ERC20.sol`](ERC20.sol) contains some code snippets we want to verify the functional correctness of.
Call `kevm solc-to-k ERC20.sol ERC20 > erc20-bin-runtime.k`, to generate the helper K files.

Verification Module
-------------------

Helper module for verification tasks.

-   Add any lemmas needed for our proofs.
-   Import a large body of existing lemmas from KEVM.

```k
requires "erc20-bin-runtime.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS
    imports INFINITE-GAS
    imports EVM-OPTIMIZATIONS
    imports ERC20-BIN-RUNTIME

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
module ERC20-SPEC
    imports VERIFICATION
```

```
    claim [ERC20.name]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   ERC20.name()                 </callData>
          <k>          #execute   => #halt ...      </k>
          <output>     .ByteArray => #buf(32, NAME) </output>
          <statusCode> _          => EVMC_SUCCESS   </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires NAME_KEY ==Int ERC20._name
        andBool NAME     ==Int #lookup(ACCT_STORAGE, NAME_KEY)
```

```
    claim [ERC20.decimals]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   ERC20.decimals()                 </callData>
          <k>          #execute   => #halt ...          </k>
          <output>     .ByteArray => #buf(32, DECIMALS) </output>
          <statusCode> _          => EVMC_SUCCESS       </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires DECIMALS_KEY ==Int ERC20._decimals
        andBool DECIMALS     ==Int 255 &Int #lookup(ACCT_STORAGE, DECIMALS_KEY)
```

```
    claim [ERC20.totalSupply]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   ERC20.totalSupply()                 </callData>
          <k>          #execute   => #halt ...             </k>
          <output>     .ByteArray => #buf(32, TOTALSUPPLY) </output>
          <statusCode> _          => EVMC_SUCCESS          </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires TOTALSUPPLY_KEY ==Int ERC20._totalSupply
        andBool TOTALSUPPLY     ==Int #lookup(ACCT_STORAGE,  TOTALSUPPLY_KEY)
```

```
    claim [ERC20.balanceOf]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   ERC20.balanceOf(ACCOUNT)          </callData>
          <k>          #execute   => #halt ...           </k>
          <output>     .ByteArray => #buf(32, BALANCEOF) </output>
          <statusCode> _          => EVMC_SUCCESS        </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires BALANCEOF_KEY ==Int ERC20._balances[ACCOUNT]
        andBool BALANCEOF     ==Int #lookup(ACCT_STORAGE, BALANCEOF_KEY)
```

```k
    claim [ERC20.transfer.success.1]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>
          <static>    false                                      </static>

          <id>         ACCTID      => ?_ </id>
          <caller>     OWNER       => ?_ </caller>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <substate> _             => ?_ </substate>

          <callData>   ERC20.transfer(TO, AMOUNT) </callData>
          <k>          #execute   => #halt ...    </k>
          <output>     .ByteArray => #buf(32, 1)  </output>
          <statusCode> _          => EVMC_SUCCESS </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE => ?ACCT_STORAGE </storage>
            ...
          </account>

       requires FROM_KEY    ==Int ERC20._balances[OWNER]
        andBool TO_KEY      ==Int ERC20._balances[TO]
        andBool FROM_BEFORE ==Int #lookup(ACCT_STORAGE, FROM_KEY)
        andBool TO_BEFORE   ==Int #lookup(ACCT_STORAGE, TO_KEY)

        andBool #rangeAddress(OWNER)
        andBool #rangeAddress(SPENDER)
        andBool #rangeUInt(256, AMOUNT)
        andBool OWNER =/=Int 0
        andBool SPENDER =/=Int 0

        ensures ?FROM_AFTER  ==Int #lookup(?ACCT_STORAGE, FROM_KEY)
        andBool ?TO_AFTER    ==Int #lookup(?ACCT_STORAGE, TO_KEY)
        andBool ?FROM_AFTER  ==Int FROM_BEFORE -Int AMOUNT
        andBool ?TO_AFTER    ==Int TO_BEFORE   +Int AMOUNT
```

```
    claim [ERC20.allowance]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>

          <id>         ACCTID      => ?_ </id>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>

          <callData>   ERC20.allowance(ACCOUNT, SPENDER) </callData>
          <k>          #execute   => #halt ...           </k>
          <output>     .ByteArray => #buf(32, ALLOWANCE) </output>
          <statusCode> _          => EVMC_SUCCESS        </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE </storage>
            ...
          </account>

       requires ALLOWANCE_KEY ==Int ERC20._allowances[ACCOUNT][SPENDER]
        andBool ALLOWANCE     ==Int #lookup(ACCT_STORAGE, ALLOWANCE_KEY)
```

```
    claim [ERC20.approve.success]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>
          <static>    false                                      </static>

          <id>         ACCTID      => ?_ </id>
          <caller>     OWNER       => ?_ </caller>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <substate> _             => ?_ </substate>

          <callData>   ERC20.approve(SPENDER, AMOUNT) </callData>
          <k>          #execute   => #halt ...        </k>
          <output>     .ByteArray => #buf(32, 1)      </output>
          <statusCode> _          => EVMC_SUCCESS     </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE => ACCT_STORAGE [ ALLOWANCE_KEY <- AMOUNT ] </storage>
            ...
          </account>

       requires ALLOWANCE_KEY ==Int ERC20._allowances[OWNER][SPENDER]
        andBool #rangeAddress(OWNER)
        andBool #rangeAddress(SPENDER)
        andBool #rangeUInt(256, AMOUNT)
        andBool OWNER =/=Int 0
        andBool SPENDER =/=Int 0
```

```
    claim [ERC20.approve.revert]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>
          <static>    false                                      </static>

          <id>         ACCTID      => ?_ </id>
          <caller>     OWNER       => ?_ </caller>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <substate> _             => ?_ </substate>

          <callData>   ERC20.approve(SPENDER, AMOUNT) </callData>
          <k>          #execute   => #halt ...        </k>
          <output>     _          => ?_               </output>
          <statusCode> _          => EVMC_REVERT      </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> _ACCT_STORAGE </storage>
            ...
          </account>

       requires #rangeAddress(OWNER)
        andBool #rangeAddress(SPENDER)
        andBool #rangeUInt(256, AMOUNT)
        andBool (OWNER ==Int 0 orBool SPENDER ==Int 0)
```

```
    claim [ERC20.transferFrom.success.1]:
          <mode>     NORMAL   </mode>
          <schedule> ISTANBUL </schedule>

          <callStack> .List                                      </callStack>
          <program>   #binRuntime(ERC20)                         </program>
          <jumpDests> #computeValidJumpDests(#binRuntime(ERC20)) </jumpDests>
          <static>    false                                      </static>

          <id>         ACCTID      => ?_ </id>
          <caller>     OWNER       => ?_ </caller>
          <localMem>   .Memory     => ?_ </localMem>
          <memoryUsed> 0           => ?_ </memoryUsed>
          <wordStack>  .WordStack  => ?_ </wordStack>
          <pc>         0           => ?_ </pc>
          <endPC>      _           => ?_ </endPC>
          <gas>        #gas(_VGAS) => ?_ </gas>
          <callValue>  0           => ?_ </callValue>
          <substate> _             => ?_ </substate>

          <callData>   ERC20.transferFrom(FROM, TO, AMOUNT) </callData>
          <k>          #execute   => #halt ...              </k>
          <output>     .ByteArray => #buf(32, 1)            </output>
          <statusCode> _          => EVMC_SUCCESS           </statusCode>

          <account>
            <acctID> ACCTID </acctID>
            <storage> ACCT_STORAGE => ?ACCT_STORAGE </storage>
            ...
          </account>

       requires FROM_KEY    ==Int ERC20._balances[FROM]
        andBool TO_KEY      ==Int ERC20._balances[TO]
        andBool FROM_BEFORE ==Int #lookup(ACCT_STORAGE, FROM_KEY)
        andBool TO_BEFORE   ==Int #lookup(ACCT_STORAGE, TO_KEY)

        andBool #rangeAddress(OWNER)
        andBool #rangeAddress(SPENDER)
        andBool #rangeUInt(256, AMOUNT)
        andBool OWNER =/=Int 0
        andBool SPENDER =/=Int 0
        andBool TO =/=Int 0

        ensures ?FROM_AFTER  ==Int #lookup(?ACCT_STORAGE, FROM_KEY)
        andBool ?TO_AFTER    ==Int #lookup(?ACCT_STORAGE, TO_KEY)
        andBool ?FROM_AFTER  ==Int FROM_BEFORE -Int AMOUNT
        andBool ?TO_AFTER    ==Int TO_BEFORE   +Int AMOUNT
```

```k
endmodule
```
