EVM Semantics
=============

```k
requires "evm-syntax.k"
```

We need to define the configuration before defining the semantics of any rules
which span multiple cells.

```k
module EVM-CONFIGURATION
    imports EVM-SYNTAX

    configuration <T>
                    // local execution
                    <k> $PGM:EVMSimulation </k>
                    <id> .AcctID </id>
                    <pc> 0:Word </pc>
                    <gas> 0:Word </gas>
                    <wordStack> .WordStack </wordStack>
                    <localMem> .Map </localMem>
                    <gasPrice> 0:Word </gasPrice>
                    // suspended processes
                    <callStack> .CallStack </callStack>
                    // account information
                    <accounts>
                        <account multiplicity="*">
                            <acctID> .AcctID </acctID>
                            <nonce> 0:Word </nonce>
                            <balance> 0:Word </balance>
                            <program> .Map </program>
                            <storage> .Map </storage>
                        </account>
                    </accounts>
                  </T>
endmodule
```

Machine Operation Utilities
---------------------------

### Utilities

We'll start with some helpers which do "standard" things to our configuration.
These will make defining `EVM-INITIALIZATION` easier, and may be useful later.

```k
module EVM-UTIL
    imports EVM-CONFIGURATION
```

We start out with setters for the `Program` and `Storage` associated to an
account. Because they are stored as maps, we have to keep a little bit of extra
state (what the next map key is) when actually running these.

```k
    syntax KItem ::= "#setAcctBalance" AcctID Word
 // ----------------------------------------------
    rule <k> #setAcctBalance ACCT BAL => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <balance> _ => BAL </balance>
            ...
         </account>
      [structural]

    syntax KItem ::= "#setAcctNonce" AcctID Word
 // --------------------------------------------
    rule <k> #setAcctNonce ACCT NONCE => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <nonce> _ => NONCE </nonce>
            ...
         </account>
      [structural]

    syntax KItem ::= "#setAcctProgram" AcctID Program
 // -------------------------------------------------
    rule <k> #setAcctProgram ACCT PGM => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <program> _ => PGM </program>
            ...
         </account>
      [structural]

    syntax KItem ::= "#setAcctStorage" AcctID Storage
 // -------------------------------------------------
    rule <k> #setAcctStorage ACCT STORAGE => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <storage> _ => STORAGE </storage>
            ...
         </account>
      [structural]

    syntax KItem ::= "#increaseAcctBalance" AcctID Word [strict(2)]
 // ---------------------------------------------------------------
    rule #increaseAcctBalance .AcctID BAL => . [structural]
    rule <k> #increaseAcctBalance ACCT BAL => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <balance> X => X +Word BAL </balance>
            ...
         </account>
      [structural]

    syntax KItem ::= "#decreaseAcctBalance" AcctID Word [strict(2)]
 // ---------------------------------------------------------------
    rule #decreaseAcctBalance .AcctID BAL => . [structural]
    rule <k> #decreaseAcctBalance ACCT BAL => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <balance> X => X -Word BAL </balance>
            ...
         </account>
      [structural]
```

The next setters allow setting information about the current running process,
and are useful at initialization as well as when `CALL` or `RETURN` is invoked.

```k
    syntax KItem ::= "#setAccountID" AcctID
 // ---------------------------------------
    rule <k> #setAccountID ACCTID => . ... </k>
         <id> _ => ACCTID </id>
      [structural]

    syntax KItem ::= "#setProgramCounter" Word
 // ------------------------------------------
    rule <k> #setProgramCounter PCOUNT => . ... </k>
         <pc> _ => PCOUNT </pc>
      [structural]

    syntax KItem ::= "#setGasAvail" Word
 // ------------------------------------
    rule <k> #setGasAvail GASAVAIL => . ... </k>
         <gas> _ => GASAVAIL </gas>
      [structural]

    syntax KItem ::= "#setGasPrice" Word
 // ------------------------------------
    rule <k> #setGasPrice PRICE => . ... </k>
         <gasPrice> _ => PRICE </gasPrice>
      [structural]

    syntax KItem ::= "#setWordStack" WordStack
 // ------------------------------------------
    rule <k> #setWordStack WS => . ... </k>
         <wordStack> _ => WS </wordStack>
      [structural]

    syntax KItem ::= "#setLocalMem" WordMap
 // ---------------------------------------
    rule <k> #setLocalMem LM => . ... </k>
         <localMem> _ => LM </localMem>
      [structural]

    syntax KItem ::= "#updateLocalMem" Word WordStack
 // -------------------------------------------------
    rule <k> #updateLocalMem N WL => #setLocalMem (LM[N := WL]) ... </k>
         <localMem> LM </localMem>
      [structural]

    syntax KItem ::= "#setProcess" Process
 // --------------------------------------
    rule #setProcess { ACCT | PCOUNT | GASAVAIL | WS | LM }
         =>    #setAccountID ACCT
            ~> #setProgramCounter PCOUNT
            ~> #setGasAvail GASAVAIL
            ~> #setWordStack WS
            ~> #setLocalMem LM
      [structural]

    syntax KItem ::= "#pushCallStack"
 // ---------------------------------
    rule <k> #pushCallStack => . ... </k>
         <id> ACCT </id>
         <pc> PCOUNT </pc>
         <gas> GASAVAIL </gas>
         <wordStack> WS </wordStack>
         <localMem> LM </localMem>
         <callStack> CS => { ACCT | PCOUNT | GASAVAIL | WS | LM } CS </callStack>
      [structural]

    syntax KItem ::= "#popCallStack"
 // --------------------------------
    rule <k> #popCallStack => #setProcess P ... </k>
         <callStack> P:Process CS => CS </callStack>
      [structural]
endmodule
```

Intraprocedural Execution
-------------------------

Here we define how to get operands out of the `WordStack` and into the arguments
of various operators so that the already defined operations can act on them.

```k
module EVM-INTRAPROCEDURAL
    imports EVM-CONFIGURATION
    imports EVM-UTIL
    imports EVM-GAS

    rule <k> . => OP </k>
         <id> ACCT </id>
         <pc> PCOUNT => PCOUNT +Word 1 </pc>
         <gas> G => G -Word #gas(OP) </gas>
         <account>
            <acctID> ACCT </acctID>
            <program> ... PCOUNT |-> OP ... </program>
            ...
         </account>
      requires ((G >Word #gas(OP)) ==K bool2Word(true)) orBool ((G ==Word #gas(OP)) ==K bool2Word(true))

    rule <k> UOP:UnStackOp => UOP W0 ... </k>
         <wordStack> W0 : WS => WS </wordStack>
      [structural]

    rule <k> BOP:BinStackOp => BOP W0 W1 ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>
      [structural]

    rule <k> TOP:TernStackOp => TOP W0 W1 W2 ... </k>
         <wordStack> W0 : W1 : W2 : WS => WS </wordStack>
      [structural]

    rule <k> QOP:QuadStackOp => QOP W0 W1 W2 W3 ... </k>
         <wordStack> W0 : W1 : W2 : W3 : WS => WS </wordStack>
      [structural]

    rule <k> W0:Word ~> #push => . ... </k>
         <wordStack> WS => W0 : WS </wordStack>
      [structural]

    rule <k> #checkStackSize => #stackSize(WS) ~> #checkStackSize ... </k>
         <wordStack> WS </wordStack>
      [structural]

    rule MSTORE INDEX VALUE => #updateLocalMem INDEX (VALUE : .WordStack)
      [structural]
    rule <k> MLOAD INDEX => VALUE ~> #push ... </k>
         <localMem> ... INDEX |-> VALUE ... </localMem>
      [structural]

    rule <k> DUP [ N ] => WS[N -Word 1] ~> #push ~> #checkStackSize </k>
         <wordStack> WS </wordStack>
         requires ((N >Word 0) ==K bool2Word(true)) andBool ((N <Word 17) ==K bool2Word(true))
      [structural]

    rule JUMP DEST => #setProgramCounter DEST    [structural]
    rule JUMP1 DEST 0 => .                       [structural]
    rule JUMP1 DEST N => #setProgramCounter DEST [owise, structural]
endmodule
```

Interprocedural Execution
-------------------------

Here we give the semantics to operations which communicate/call between accounts
on the network.

```k
module EVM-INTERPROCEDURAL
    imports EVM-INTRAPROCEDURAL

    syntax KItem ::= "#processCall" "{" AcctID "|" Word "|" WordStack "}"
 // ---------------------------------------------------------------------
    rule <k> CALL ACCT ETHER INIT SIZE => #processCall { ACCT | ETHER | #range(LM, INIT, SIZE) } ... </k>
         <localMem> LM </localMem>
      [structural]

    // TODO: How are we handling refunding unused gas?
    rule <k> #processCall {ACCT | ETHER | WL}
          =>    #pushCallStack
             ~> #setProcess {ACCT | 0 | ETHER | .WordStack | #asMap(WL)}
         ... </k>
         <id> CURRACCT </id>
      [structural]

    syntax KItem ::= "#processReturn" WordStack
 // -------------------------------------------
    rule #processReturn WL => #popCallStack ~> #returnValues WL
      [structural]
    rule <k> RETURN INIT SIZE => #processReturn #range(LM, INIT, SIZE) ... </k>
         <localMem> LM </localMem>
      [structural]

    syntax KItem ::= "#returnValues" WordStack
 // ------------------------------------------
    rule <k> #returnValues WL => #updateLocalMem INIT #take(SIZE, WL) ... </k>
         <wordStack> INIT : SIZE : WS => WS </wordStack>
      [structural]

    syntax KItem ::= "#newAccount" AcctID
 // -------------------------------------
    rule <k> #newAccount ACCT => . ... </k>
         <accounts>
            ...
            (.Bag
            => <account>
                    <acctID> ACCT </acctID>
                    <nonce> 0:Word </nonce>
                    <balance> 0:Word </balance>
                    <program> .Map </program>
                    <storage> .Map </storage>
               </account>
            )
         </accounts>
      [structural]
endmodule
```

Initialization and Running
--------------------------

Actual initialization is easy now, we just have to desugar the top-level syntax
into setting up the accounts (using our helpers), then setting the correct
process (also using the helpers).

```k
module EVM
    imports EVM-INTERPROCEDURAL

    rule account: - id      : ACCT
                  - nonce   : NONCE
                  - balance : BAL
                  - program : PROGRAM
                  - storage : STORAGE
      =>    #newAccount ACCT
         ~> #setAcctNonce   ACCT NONCE
         ~> #setAcctProgram ACCT #program(PROGRAM)
         ~> #setAcctStorage ACCT #storage(STORAGE)
         ~> #setAcctBalance ACCT BAL
      [structural]

    rule transaction: - to       : ACCTTO
                      - from     : ACCTFROM
                      - data     : ARGS
                      - value    : VALUE
                      - gasPrice : PRICE
                      - gasLimit : GASAVAIL
      =>    #decreaseAcctBalance ACCTFROM VALUE
         ~> #increaseAcctBalance ACCTTO VALUE
         ~> #setGasPrice PRICE
         ~> #setProcess {ACCTTO | 0 | GASAVAIL | .WordStack | #asMap(ARGS)}
      [structural]
endmodule
```
