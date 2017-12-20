KEVM Verification
=================

Using K's reachability logic theorem prover, we're able to verify many properties about EVM programs as reachability claims.
This module defines some helpers which make writing specifications simpler.

```{.k .java}
requires "evm.k"

module VERIFICATION
    imports EVM
```

This `smt-lemma` helps Z3 reason about stack over/under flow.

```{.k .java}
    rule #sizeWordStack ( _ , _ ) >=Int 0 => true [smt-lemma]
    rule #sizeWordStack ( WS , N:Int )
      => #sizeWordStack ( WS , 0 ) +Int N
      requires N =/=K 0
      [lemma]

    rule (X -Int A) -Int B    => X -Int (A +Int B)    [smt-lemma]
    rule ((X -Int A) >=Int B) => (X >=Int (A +Int B)) [smt-lemma]
    rule (N +Int X <Int M)    => X <Int (M -Int N)    [smt-lemma]
```

Sum to N
--------

As a demonstration of simple reachability claims involing a circularity, we prove the EVM [Sum to N](proofs/sum-to-n.md) program correct.
This program sums the numbers from 1 to N (for sufficiently small N), including pre-conditions dis-allowing integer under/overflow and stack overflow.

```{.k .java}
    syntax Map ::= "sumTo" "(" Int ")" [function]
 // ---------------------------------------------
    rule sumTo(N)
      => #asMapOpCodes( PUSH(1, 0) ; PUSH(32, N)                // s = 0 ; n = N
                      ; JUMPDEST                                // label:loop
                      ; DUP(1) ; ISZERO ; PUSH(1, 52) ; JUMPI   // if n == 0, jump to end
                      ; DUP(1) ; SWAP(2) ; ADD                  // s = s + n
                      ; SWAP(1) ; PUSH(1, 1) ; SWAP(1) ; SUB    // n = n - 1
                      ; PUSH(1, 35) ; JUMP                      // jump to loop
                      ; JUMPDEST                                // label:end
                      ; .OpCodes
                      ) [macro]
```

Hacker Gold (HKG) Token Smart Contract
--------------------------------------

Several proofs about the [HKG Token functions](proofs/hkg.md) have been performed.
These helper constants make writing the proof claims simpler/cleaner.

```{.k .java}
    syntax Int ::= "%ACCT_1_BALANCE" [function]
                 | "%ACCT_2_BALANCE" [function]
                 | "%ACCT_1_ALLOWED" [function]
                 | "%ACCT_2_ALLOWED" [function]
                 | "%ACCT_ID"        [function]
                 | "%CALLER_ID"      [function]
                 | "%ORIGIN_ID"      [function]
                 | "%COINBASE_VALUE" [function]

    rule %ACCT_1_ALLOWED => 90140393717854041204577419487481777019768054268415728047989462811209962694062 [macro]
    rule %ACCT_2_BALANCE => 7523342389551220067180060596052511116626922476768911452708464109912271601147  [macro]
    rule %ACCT_1_BALANCE => 73276140668783822097736045772311176946506324369098798920944620499663575949472 [macro]
    rule %ACCT_2_ALLOWED => 89883370637028415006891042932604780869171597379948077832163656920795299088269 [macro]
    rule %ACCT_ID        => 87579061662017136990230301793909925042452127430                               [macro]
    rule %CALLER_ID      => 428365927726247537526132020791190998556166378203                              [macro]
    rule %ORIGIN_ID      => 116727156174188091019688739584752390716576765452                              [macro]
    rule %COINBASE_VALUE => 244687034288125203496486448490407391986876152250                              [macro]
    syntax WordStack ::= "%HKG_ProgramBytes"       [function]
                       | "%HKG_ProgramBytes_buggy" [function]
    syntax Map ::= "%HKG_Program"       [function]
                 | "%HKG_Program_buggy" [function]

    rule %HKG_ProgramBytes       => #parseByteStack("0x60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461006757806323b872dd146100be57806370a0823114610134578063a9059cbb1461017e578063dd62ed3e146101d5575bfe5b341561006f57fe5b6100a4600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061023e565b604051808215151515815260200191505060405180910390f35b34156100c657fe5b61011a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610331565b604051808215151515815260200191505060405180910390f35b341561013c57fe5b610168600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105b2565b6040518082815260200191505060405180910390f35b341561018657fe5b6101bb600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919080359060200190919050506105fc565b604051808215151515815260200191505060405180910390f35b34156101dd57fe5b610228600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff1690602001909190505061076a565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a3600190505b92915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002054101580156103fe575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b801561040a5750600082115b156105a15781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254019250508190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105ab565b600090506105ab565b5b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015801561064d5750600082115b1561075a5781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825401925050819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a360019050610764565b60009050610764565b5b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b929150505600a165627a7a72305820955d4848f79dc023af4f6c233535c5c8d39532ebe7e7b64adbd933112556edf30029")                 [macro]
    rule %HKG_ProgramBytes_buggy => #parseByteStack("60606040526000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff168063095ea7b31461006a57806323b872dd146100c457806370a082311461013d578063a9059cbb1461018a578063dd62ed3e146101e4575b600080fd5b341561007557600080fd5b6100aa600480803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610250565b604051808215151515815260200191505060405180910390f35b34156100cf57600080fd5b610123600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091908035906020019091905050610343565b604051808215151515815260200191505060405180910390f35b341561014857600080fd5b610174600480803573ffffffffffffffffffffffffffffffffffffffff169060200190919050506105c4565b6040518082815260200191505060405180910390f35b341561019557600080fd5b6101ca600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803590602001909190505061060e565b604051808215151515815260200191505060405180910390f35b34156101ef57600080fd5b61023a600480803573ffffffffffffffffffffffffffffffffffffffff1690602001909190803573ffffffffffffffffffffffffffffffffffffffff16906020019091905050610773565b6040518082815260200191505060405180910390f35b600081600260003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167f8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925846040518082815260200191505060405180910390a3600190505b92915050565b600081600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410158015610410575081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205410155b801561041c5750600082115b156105b35781600160008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254019250508190555081600260008673ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020600082825403925050819055508273ffffffffffffffffffffffffffffffffffffffff168473ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a3600190506105bd565b600090506105bd565b5b9392505050565b6000600160008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b919050565b600081600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020541015801561065f5750600082115b156107635781600160003373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000206000828254039250508190555081600160008573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff168152602001908152602001600020819055508273ffffffffffffffffffffffffffffffffffffffff163373ffffffffffffffffffffffffffffffffffffffff167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef846040518082815260200191505060405180910390a36001905061076d565b6000905061076d565b5b92915050565b6000600260008473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff16815260200190815260200160002060008373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020016000205490505b929150505600a165627a7a7230582093e640afb442869193a08cf82ed9577e403c7c53a6a95f589e2b673195da102e0029") [macro]
    rule %HKG_Program => #asMapOpCodes(#dasmOpCodes(%HKG_ProgramBytes, DEFAULT))
    rule %HKG_Program_buggy => #asMapOpCodes(#dasmOpCodes(%HKG_ProgramBytes_buggy, DEFAULT))

endmodule
```
