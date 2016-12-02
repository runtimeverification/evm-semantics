---
title: K Model of EVM Execution Environment
geometry: margin=2.5cm
...


```k
requires "evm-data.k"
```

None of the rules defined here should be sensitive to other parts of the
configuration, they should be standalone.


Local Execution State
=====================

EVM execution maintains some local state (like a word stack, local memory,
program counter, etc...). We need to specify the syntax of all this local state
for storage.

Stack Operations
----------------

We break up stack operations into groups by their arity so that we can pull out
the correct number of arguments for each operation.

NOTE: We have to call the opcode `OR` by `EVMOR` instead, because otherwise K
has trouble parsing it/compiling the definition.

The `Null`, `Un`, `Bin`, and `Tern` refer to the number of elements that each
operation takes off the stack. These are binned in this way so that we can have
simpler rules (in the semantics) for pulling items off the stacks.

```k
module EVM-STACK-OPERATORS
    imports EVM-WORD

    syntax NullStackOp ::= "#push"
                         | "PUSH" Word
                         | "#checkStackSize"
                         | "STACK_OVERFLOW"
    syntax KItem ::= NullStackOp

    rule PUSH N => N ~> #push ~> #checkStackSize [structural]
    rule (I:Int ~> #checkStackSize) => .              requires I <Int  1024
    rule (I:Int ~> #checkStackSize) => STACK_OVERFLOW requires I >=Int 1024

    syntax UnStackOp ::= "ISZERO" | "NOT" | "POP"
    syntax KItem ::= UnStackOp Word

    rule ISZERO 0 => bool2Word(true)  ~> #push                   [structural]
    rule ISZERO N => bool2Word(false) ~> #push requires N =/=K 0 [structural]
    rule NOT    N => bitwisenot(N)    ~> #push                   [structural]
    rule POP    N => .                                           [structural]

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP"
                        | "MOD" | "SIGNEXTEND" | "SDIV" | "SMOD"
                        | "LT" | "GT" | "SLT" | "SGT" | "EQ"
                        | "AND" | "EVMOR" | "XOR"
                        | "BYTE" | "SHA3"
    syntax KItem ::= BinStackOp Word Word

    rule ADD        W0 W1 => W0 +Word W1       ~> #push [structural]
    rule MUL        W0 W1 => W0 *Word W1       ~> #push [structural]
    rule SUB        W0 W1 => W0 -Word W1       ~> #push [structural]
    rule DIV        W0 W1 => W0 /Word W1       ~> #push [structural]
    rule EXP        W0 W1 => W0 ^Word W1       ~> #push [structural]
    rule MOD        W0 W1 => W0 %Word W1       ~> #push [structural]
    rule SIGNEXTEND W0 W1 => signextend(W0,W1) ~> #push [structural]
    rule SDIV       W0 W1 => sdiv(W0,W1)       ~> #push [structural]
    rule SMOD       W0 W1 => smod(W0,W1)       ~> #push [structural]
    rule LT         W0 W1 => W0 <Word W1       ~> #push [structural]
    rule GT         W0 W1 => W0 >Word W1       ~> #push [structural]
    rule SLT        W0 W1 => slt(W0,W1)        ~> #push [structural]
    rule SGT        W0 W1 => sgt(W0,W1)        ~> #push [structural]
    rule EQ         W0 W1 => W0 ==Word W1      ~> #push [structural]
    rule AND        W0 W1 => bitwiseand(W0,W1) ~> #push [structural]
    rule EVMOR      W0 W1 => bitwiseor(W0,W1)  ~> #push [structural]
    rule XOR        W0 W1 => bitwisexor(W0,W1) ~> #push [structural]
    rule BYTE       W0 W1 => getbyte(W0,W1)    ~> #push [structural]
    rule SHA3       W0 W1 => sha3(W0,W1)       ~> #push [structural]

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
    syntax KItem ::= TernStackOp Word Word Word

    rule ADDMOD W0 W1 W2 => addmod(W0,W1,W2) [structural]
    rule MULMOD W0 W1 W2 => mulmod(W0,W1,W2) [structural]

    syntax StackOp ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp
endmodule
```

EVM Programs
------------

```k
module EVM-PROGRAM-SYNTAX
    imports EVM-STACK-OPERATORS

    syntax LocalOp   ::= StackOp | "MLOAD" | "MSTORE" | "MLOAD8"
    syntax ProcessOp ::= "CALL" | "RETURN"
    syntax OpCode    ::= LocalOp | ProcessOp

    syntax Program ::= List{OpCode, ";"}
endmodule
```

EVM Accounts
------------

EVM `Account`s contain the `AcctID` (account identifier), the `Balance` (amount
of ether in the account), the `Storage` (long-term memory of the account), and
the `Program` (code of the account). We use a YAML-like notation to specify
them, as shown here:

```evm-account
account:
-   id: 15
-   balance: 40
-   program: PUSH 30 ; PUSH 35 ; ADD
-   storage: 50 , 70 , 82
```

```k
module EVM-ACCOUNT-SYNTAX
    imports EVM-PROGRAM-SYNTAX

    syntax AcctID  ::= Word | ".AcctID"
    syntax Storage ::= List{Word,","}

    syntax Account ::= "account" ":"
                       "-" "id" ":" AcctID
                       "-" "balance" ":" Word
                       "-" "program" ":" Program
                       "-" "storage" ":" Storage

    syntax AccountState ::=     "balance" ":" Word
                            "," "program" ":" Map
                            "," "storage" ":" Map

endmodule
```

EVM Process
-----------

The `WordStack` is the size-limited (to 1024) stack of words that each local
execution of an EVM process has acess to. The `LocalMem` is an array of memory
it has local access to (modeled here as a map from addresses to values). EVM
Processes are tuples of their associated `PID`, their `ProgramCounter`, their
`WordStack`, and their `LocalMem`.

```k
module EVM-PROCESS-SYNTAX
    imports EVM-ACCOUNT-SYNTAX

    syntax WordStack ::= ".WordStack"
                       | Word ":" WordStack

    syntax KItem ::= "#stackSize" WordStack
                   | "#stackUnit"

    rule #stackSize .WordStack => 0                         [structural]
    rule #stackSize (W : WS) => #stackSize WS ~> #stackUnit [structural]
    rule I1:Int ~> #stackUnit => I1 +Int 1                  [structural]

    syntax LocalMem ::= Map | ".LocalMem"

    syntax Process ::= "{" AcctID "|" Word "|" WordStack "|" LocalMem "}"
    syntax CallStack ::= ".CallStack"
                       | Process CallStack

    rule .LocalMem => .Map [macro]
    syntax MergeMemOp ::= "#mergeMem" "{" Word "|"  Word "|" Word "|" LocalMem "}" [function]
                          | LocalMem

endmodule
```

EVM Simulation
--------------

We need a way to specify the current world state. It will be a list of accounts,
along with which account to call execution on first:

```k
module EVM-SYNTAX
    imports EVM-ACCOUNT-SYNTAX
    imports EVM-PROCESS-SYNTAX

    syntax Accounts ::= ".Accounts"
                      | Account Accounts

    syntax EVMSimulation ::= Accounts "START" AcctID
endmodule
```
