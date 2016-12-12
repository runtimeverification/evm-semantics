Configuration
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
                    <pc> 0 </pc>
                    <gas> 0 </gas>
                    <wordStack> .WordStack </wordStack>
                    <localMem> .Map </localMem>
                    <gasPrice> 0 </gasPrice>
                    // suspended processes
                    <callStack> .CallStack </callStack>
                    // account information
                    <accounts>
                        <account multiplicity="*">
                            <acctID> .AcctID </acctID>
                            <program> .Map </program>
                            <storage> .Map </storage>
                            <balance> 0:Word </balance>
                        </account>
                    </accounts>
                  </T>
endmodule
```

Machine Operation
-----------------

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
    syntax KItem ::= "#setAcctProgram" AcctID Program
                   | "#setAcctProgram" AcctID Int Program
                   | "#setAcctStorage" AcctID WordMap
                   | "#increaseAcctBalance" AcctID Word      [strict(2)]
                   | "#decreaseAcctBalance" AcctID Word      [strict(2)]

    rule #setAcctProgram ACCT PGM => #setAcctProgram ACCT 0 PGM
    rule #setAcctProgram ACCT N .Program => .
    rule <k> #setAcctProgram ACCT N (OP:OpCode ; PGM)
          => #setAcctProgram ACCT (N +Int 1) PGM
         ... </k>
         <account>
            <acctID> ACCT </acctID>
            <program> PROGRAM => PROGRAM[N <- OP] </program>
            ...
         </account>

    rule <k> #setAcctStorage ACCT WM => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <storage> _ => WM </storage>
            ...
         </account>

    rule <k> #increaseAcctBalance ACCT Balance => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <balance> X => X +Word Balance </balance>
            ...
         </account>

    rule <k> #decreaseAcctBalance ACCT Balance => . ... </k>
         <account>
            <acctID> ACCT </acctID>
            <balance> X => X -Word Balance </balance>
            ...
         </account>
```

The next setters allow setting information about the current running process,
and are useful at initialization as well as when `CALL` or `RETURN` is invoked.

```k
    syntax KItem ::= "#setAccountID" AcctID
                   | "#setProgramCounter" Int
                   | "#setGasAvail" Int
                   | "#setGasPrice" Int
                   | "#setWordStack" WordStack
                   | "#setLocalMem" WordMap
                   | "#updateLocalMem" Int WordList
                   | "#setProcess" Process
                   | "#pushCallStack"
                   | "#popCallStack"

    rule <k> #setAccountID ACCTID => . ... </k>
         <id> _ => ACCTID </id>

    rule <k> #setProgramCounter PCOUNT => . ... </k>
         <pc> _ => PCOUNT </pc>

    rule <k> #setGasAvail GASAVAIL => . ... </k>
         <gas> _ => GASAVAIL </gas>

    rule <k> #setGasPrice PRICE => . ... </k>
         <gasPrice> _ => PRICE </gasPrice>

    rule <k> #setWordStack WS => . ... </k>
         <wordStack> _ => WS </wordStack>

    rule <k> #setLocalMem LM => . ... </k>
         <localMem> _ => LM </localMem>

    rule <k> #updateLocalMem N WL => #setLocalMem (LM[N := WL]) ... </k>
         <localMem> LM </localMem>

    rule #setProcess { ACCT | PCOUNT | GASAVAIL | WS | LM }
         =>    #setAccountID ACCT
            ~> #setProgramCounter PCOUNT
            ~> #setGasAvail GASAVAIL
            ~> #setWordStack WS
            ~> #setLocalMem LM

    rule <k> #pushCallStack => . ... </k>
         <id> ACCT </id>
         <pc> PCOUNT </pc>
         <gas> GASAVAIL </gas>
         <wordStack> WS </wordStack>
         <localMem> LM </localMem>
         <callStack> CS => { ACCT | PCOUNT | GASAVAIL | WS | LM } CS </callStack>

    rule <k> #popCallStack => #setProcess P ... </k>
         <callStack> P:Process CS => CS </callStack>
endmodule
```

Here we define how to get operands out of the `WordStack` and into the arguments
of various operators so that the already defined operations can act on them.

```k
module EVM-INTRAPROCEDURAL
    imports EVM-CONFIGURATION
    imports EVM-UTIL

    rule <k> . => OP </k>
         <id> ACCT </id>
         <pc> PCOUNT => PCOUNT +Int 1 </pc>
         <gas> G => G +Int #gas( OP ) </gas>
         <account>
            <acctID> ACCT </acctID>
            <program> ... PCOUNT |-> OP ... </program>
            ...
         </account>

    rule <k> UOP:UnStackOp => UOP W0 ... </k>
         <wordStack> W0 : WS => WS </wordStack>

    rule <k> BOP:BinStackOp => BOP W0 W1 ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>

    rule <k> TOP:TernStackOp => TOP W0 W1 W2 ... </k>
         <wordStack> W0 : W1 : W2 : WS => WS </wordStack>

    rule <k> W0:Int ~> #push => . ... </k>
         <wordStack> WS => W0 : WS </wordStack>

    rule <k> #checkStackSize => #stackSize WS ~> #checkStackSize ... </k>
         <wordStack> WS </wordStack>

    rule <k> MSTORE => #updateLocalMem INDEX VALUE ... </k>
         <wordStack> INDEX : VALUE : WS => WS </wordStack>

    rule <k> MLOAD => . ... </k>
         <wordStack> INDEX : WS => VALUE : WS </wordStack>
         <localMem>... INDEX |-> VALUE ...</localMem>

    rule <k> DUP N => WS[N -Int 1] ~> #push ~> #checkStackSize </k>
         <wordStack> WS </wordStack>
         requires N >Int 0 andBool N <=Int 16

    rule <k> JUMP => #setProgramCounter W0 ... </k>
         <wordStack> W0 : WS => WS </wordStack>

    rule <k> JUMP1 => . ...</k> 
         <wordStack> _ : W1 :  WS => WS </wordStack>
         requires W1 ==Int 0

    rule <k> JUMP1 => #setProgramCounter W0 ...</k>
         <wordStack> W0 : W1 :  WS => WS </wordStack>
         requires notBool W1 ==Int 0
endmodule
```

```k
module EVM-INTERPROCEDURAL
    imports EVM-INTRAPROCEDURAL

    syntax KItem ::= "#processCall" "{" AcctID "|" Word "|" WordList "}"
                   | "#processReturn" WordList [strict]

    rule <k> CALL => #processCall { ACCT | ETHER | #range(LM, INIT, SIZE) } ... </k>
         <wordStack> ACCT : ETHER : INIT : SIZE : WS => WS </wordStack>
         <localMem> LM </localMem>

    // TODO: How are we handling refunding unused gas?
    rule <k> #processCall {ACCT | ETHER | WL}
          =>    #pushCallStack
             ~> #setProcess {ACCT | 0 | ETHER | .WordStack | #asMap(WL)}
         ... </k>
         <id> CURRACCT </id>

    rule <k> RETURN => #processReturn #range(LM, INIT, SIZE) ... </k>
         <wordStack> (INIT : SIZE : WS) => WS </wordStack>
         <localMem> LM </localMem>

    syntax KItem ::= "#returnValues" WordList

    rule #processReturn WL => #popCallStack ~> #returnValues WL

    rule <k> #returnValues WL => #updateLocalMem INIT #take(SIZE, WL) ... </k>
         <wordStack> INIT : SIZE : WS => WS </wordStack>
endmodule
```

### Initialization and Running

Actual initialization is easy now, we just have to desugar the top-level syntax
into setting up the accounts (using our helpers), then setting the correct
process (also using the helpers).

```k
module EVM
    imports EVM-UTIL
    imports EVM-INTERPROCEDURAL

    rule <k> account:
             -   id: ACCT
             -   balance: BALANCE
             -   program: PROGRAM
             -   storage: STORAGE
          =>    #setAcctStorage ACCT #asMap(STORAGE)
             ~> #setAcctProgram ACCT PROGRAM
             ...
         </k>
         <accounts>
            ...
            (.Bag
            => <account>
                    <acctID> ACCT </acctID>
                    <program> .Map </program>
                    <storage> .Map </storage>
                    <balance> BALANCE </balance>
               </account>
            )
         </accounts>

    rule transaction:
         -   to: ACCTTO
         -   from: ACCTFROM
         -   data: ARGS
         -   value: VALUE
         -   gasPrice: PRICE
         -   gasLimit: GASAVAIL
      =>    #decreaseAcctBalance ACCTFROM VALUE
         ~> #increaseAcctBalance ACCTTO VALUE
         ~> #setGasPrice PRICE
         ~> #processCall {ACCTTO | GASAVAIL | ARGS}
endmodule
```
