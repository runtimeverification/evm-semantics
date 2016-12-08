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
                    <accountID> .AcctID </accountID>
                    <pc> 0 </pc>
                    <wordStack> .WordStack </wordStack>
                    <localMem> .WordMap </localMem>
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

Machine Initialization
----------------------

This module just takes the parsed world definition (list of accounts and account
to start with) and loads it all into the correct cells of the configuration.

### Utilities

We'll start with some helpers which do "standard" things to our configuration.
These will make defining `EVM-INITIALIZATION` easier, and may be useful later.

```k
module EVM-INITIALIZATION-UTIL
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
                   | "#setWordStack" WordStack
                   | "#setLocalMem" WordMap
                   | "#updateLocalMem" Int WordList
                   | "#setProcess" Process
                   | "#pushCallStack"
                   | "#popCallStack"

    rule <k> #setAccountID ACCTID => . ... </k>
         <accountID> _ => ACCTID </accountID>

    rule <k> #setProgramCounter PCOUNT => . ... </k>
         <pc> _ => PCOUNT </pc>

    rule <k> #setWordStack WS => . ... </k>
         <wordStack> _ => WS </wordStack>

    rule <k> #setLocalMem LM => . ... </k>
         <localMem> _ => LM </localMem>

    rule <k> #updateLocalMem N WL => . ... </k>
         <localMem> LM => LM[N := WL] </localMem>

    rule #setProcess { ACCT | PCOUNT | WS | LM }
         =>    #setAccountID ACCT
            ~> #setProgramCounter PCOUNT
            ~> #setWordStack WS
            ~> #setLocalMem LM

    rule <k> #pushCallStack => . ... </k>
         <accountID> ACCT </accountID>
         <pc> PCOUNT </pc>
         <wordStack> WS </wordStack>
         <localMem> LM </localMem>
         <callStack> CS => { ACCT | PCOUNT | WS | LM } CS </callStack>

    rule <k> #popCallStack => #setProcess P ... </k>
         <callStack> P:Process CS => CS </callStack>
endmodule
```

### Initialization

Actual initialization is easy now, we just have to desugar the top-level syntax
into setting up the accounts (using our helpers), then setting the correct
process (also using the helpers).

```k
module EVM-INITIALIZATION
    imports EVM-INITIALIZATION-UTIL

    syntax KItem ::= EVMSimulation

    rule ACCTS:Accounts START ACCT => ACCTS ~> #setProcess { ACCT | 0 | .WordStack | .WordMap }

    rule .Accounts => .
    rule ACCT:Account ACCTS:Accounts => ACCT ~> ACCTS

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
endmodule
```

Here we define how to get operands out of the `WordStack` and into the arguments
of various operators so that the already defined operations can act on them.

```k
module EVM-INTRAPROCEDURAL
    imports EVM-CONFIGURATION
    imports EVM-INITIALIZATION-UTIL

    rule <k> . => OP </k>
         <accountID> ACCT </accountID>
         <pc> PCOUNT => PCOUNT +Int 1 </pc>
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

    rule <k> DUP N => WS[N -Int 1] ~> #push ~> #checkStackSize </k>
         <wordStack> WS </wordStack>
         requires N >Int 0 andBool N <=Int 16

    rule <k> JUMP => #setProgramCounter W0 ... </k>
         <wordStack> W0 : WS => WS </wordStack>
    rule <k> JUMP1 => #if (W1 ==Int 0) #then .K #else #setProgramCounter W0 #fi ... </k>
         <wordStack> W0 : W1 : WS => WS </wordStack>
endmodule
```

```k
module EVM-INTERPROCEDURAL
    imports EVM-INTRAPROCEDURAL

    syntax KItem ::= "#processCall" "{" AcctID "|" Word "|" WordList "}"
                   | "#processReturn" WordList [strict]

    rule <k> CALL => #processCall { ACCT | ETHER | #range(LM, INIT, INIT +Int SIZE) } ... </k>
         <wordStack> ACCT : ETHER : INIT : SIZE : WS => WS </wordStack>
         <localMem> LM </localMem>

    // TODO: How are we handling refunding unused gas?
    rule <k> #processCall {ACCT | ETHER | WL}
          =>    #decreaseAcctBalance CURRACCT ETHER
             ~> #increaseAcctBalance ACCT ETHER
             ~> #pushCallStack
             ~> #setProcess {ACCT | 0 | .WordStack | #asMap(WL)}
         ... </k>
         <accountID> CURRACCT </accountID>

    rule <k> RETURN => #processReturn #range(LM, INIT, INIT +Int SIZE) ... </k>
         <wordStack> (INIT : SIZE : WS) => WS </wordStack>
         <localMem> LM </localMem>

    syntax KItem ::= "#returnValues" WordList

    rule #processReturn WL => #popCallStack ~> #returnValues WL

    rule <k> #returnValues WL => #updateLocalMem INIT #take(SIZE, WL) ... </k>
         <wordStack> INIT : SIZE : WS => WS </wordStack>
endmodule
```

```k
module EVM
    imports EVM-INITIALIZATION
    imports EVM-INTERPROCEDURAL
endmodule
```
