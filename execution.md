Local Execution State
=====================

EVM execution maintains some local state (like a word stack, local memory,
program counter, etc...). We need to specify the syntax of all this local state
for storage.

Intraprocedural Execution
-------------------------

Here we define how to get operands out of the `WordStack` and into the arguments
of various operators so that the already defined operations can act on them.

```k
requires "data.k"

module EVM-EXECUTION
    imports EVM-GAS

    configuration <evm>
                    <k> . </k>
                    <pc> 0:Word </pc>
                    <gas> 0:Word </gas>
                    <gasPrice> 0:Word </gasPrice>
                    <currentProgram> .Map </currentProgram>
                    <wordStack> .WordStack </wordStack>
                    <localMem> .Map </localMem>
                  </evm>

    rule <k> . => OP </k>
         <pc> PCOUNT => PCOUNT +Word 1 </pc>
         <gas> G => G -Word #gas(OP) </gas>
         <currentProgram> ... PCOUNT |-> OP ... </currentProgram>
      requires ((G >Word #gas(OP)) ==K bool2Word(true)) orBool ((G ==Word #gas(OP)) ==K bool2Word(true))

    rule <k> UOP:UnStackOp   => UOP W0       ... </k> <wordStack> W0 : WS           => WS </wordStack>
    rule <k> BOP:BinStackOp  => BOP W0 W1    ... </k> <wordStack> W0 : W1 : WS      => WS </wordStack>
    rule <k> TOP:TernStackOp => TOP W0 W1 W2 ... </k> <wordStack> W0 : W1 : W2 : WS => WS </wordStack>

    rule <k> W0:Word ~> #push => .                                 ... </k> <wordStack> WS => W0 : WS </wordStack>
    rule <k> #checkStackSize  => #stackSize(WS) ~> #checkStackSize ... </k> <wordStack> WS            </wordStack>

    rule <k> CALL => CALL W0 W1 W2 W3 W4 W5 W6 ... </k> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : W6 : WS => WS </wordStack>

    rule <k> SO:StackOp   => SO WS ... </k> <wordStack> WS      </wordStack>
    rule <k> #setStack WS => .     ... </k> <wordStack> _ => WS </wordStack>

    rule <k> MSTORE INDEX VALUE => .              ... </k> <localMem> LM => LM[INDEX <- VALUE] </localMem>
    rule <k> MLOAD INDEX        => VALUE ~> #push ... </k> <localMem> ... INDEX |-> VALUE ...  </localMem>

    rule <k> JUMP DEST    => . ... </k> <pc> _ => DEST </pc>
    rule <k> JUMP1 DEST 0 => . ... </k>
    rule <k> JUMP1 DEST N => . ... </k> <pc> _ => DEST </pc> requires N =/=K 0
endmodule
```

EVM Gas Cost
------------

Here we define the gas-cost of each instruction in the instruction set. Many of
the instructions gas cost is fixed and not dependent on any parts of the
configuration; for those that do have some dependence, their associated cost
must be defined after the configuration is defined.

```k
module EVM-GAS
    imports EVM-OPCODE

    syntax Word ::= #gas ( OpCode )    [function]

    syntax Word ::= "Gzero" | "Gbase" | "Gverylow" | "Glow" | "Gmid" | "Ghigh" | "Gextcode"
                  | "Gbalance" | "Gsload" | "Gjumpdest" | "Gsset" | "Gsreset" | "Rsclear"
                  | "Rself-destruct" | "Gself-destruct" | "Gcreate" | "Gcodedeposit" | "Gcall"
                  | "Gcallvalue" | "Gcallstipend" | "Gnewaccount" | "Gexp" | "Gexpbyte"
                  | "Gmemory" | "Gtxcreate" | "Gtxdatazero" | "Gtxdatanonzero" | "Gtransaction"
                  | "Glog" | "Glogdata" | "Glogtopic" | "Gsha3" | "Gsha3word" | "Gcopy" | "Gblockhash"
                  | "#gasSSTORE" | "#gasCALL" | "#gasSELFDESTRUCT"
 // --------------------------------------------------------------
    rule Gzero          => 0     [macro]
    rule Gbase          => 2     [macro]
    rule Gverylow       => 3     [macro]
    rule Glow           => 5     [macro]
    rule Gmid           => 8     [macro]
    rule Ghigh          => 10    [macro]
    rule Gextcode       => 700   [macro]
    rule Gbalance       => 400   [macro]
    rule Gsload         => 200   [macro]
    rule Gjumpdest      => 1     [macro]
    rule Gsset          => 20000 [macro]
    rule Gsreset        => 5000  [macro]
    rule Rsclear        => 15000 [macro]
    rule Rself-destruct => 24000 [macro]
    rule Gself-destruct => 5000  [macro]
    rule Gcreate        => 32000 [macro]
    rule Gcodedeposit   => 200   [macro]
    rule Gcall          => 700   [macro]
    rule Gcallvalue     => 9000  [macro]
    rule Gcallstipend   => 2300  [macro]
    rule Gnewaccount    => 25000 [macro]
    rule Gexp           => 10    [macro]
    rule Gexpbyte       => 10    [macro]
    rule Gmemory        => 3     [macro]
    rule Gtxcreate      => 32000 [macro]
    rule Gtxdatazero    => 4     [macro]
    rule Gtxdatanonzero => 68    [macro]
    rule Gtransaction   => 21000 [macro]
    rule Glog           => 375   [macro]
    rule Glogdata       => 8     [macro]
    rule Glogtopic      => 375   [macro]
    rule Gsha3          => 30    [macro]
    rule Gsha3word      => 6     [macro]
    rule Gcopy          => 3     [macro]
    rule Gblockhash     => 20    [macro]

    syntax OpCodes ::= "Wzero" | "Wbase" | "Wverylow" | "Wlow" | "Wmid" | "Whigh" | "Wextcode" | "Wcopy" | "Wcall"
 // --------------------------------------------------------------------------------------------------------------
    rule Wzero => STOP ; RETURN ; .OpCodes
    rule Wbase =>   ADDRESS ; ORIGIN ; CALLER ; CALLVALUE ; CALLDATASIZE
                  ; CODESIZE ; GASPRICE ; COINBASE ; TIMESTAMP ; NUMBER
                  ; DIFFICULTY ; GASLIMIT ; POP ; PC ; MSIZE ; GAS ; .OpCodes
    rule Wverylow =>  ADD ; SUB ; NOT ; LT ; GT ; SLT ; SGT ; EQ ; ISZERO ; AND
                    ; EVMOR ; XOR ; BYTE ; CALLDATALOAD ; MLOAD ; MSTORE ; MSTORE8
                    ; PUSH(0) ; DUP(0) ; SWAP(0) ; .OpCodes
    rule Wlow => MUL ; DIV ; SDIV ; MOD ; SMOD ; SIGNEXTEND ; .OpCodes
    rule Wmid => ADDMOD ; MULMOD ; JUMP ; JUMPI; .OpCodes
    rule Wextcode => EXTCODESIZE ; .OpCodes
    rule Wcopy => CALLDATACOPY ; CODECOPY ; .OpCodes
    rule Wcall => CALL ; CALLCODE ; DELEGATECALL ; .OpCodes

    rule #gas(SSTORE)       => #gasSSTORE                                           // INCORRECT
    rule #gas(EXP)          => Gexp                                                 // INCORRECT
    rule #gas(OP)           => Gverylow +Word Gcopy          requires OP in Wcopy   // INCORRECT
    rule #gas(EXTCODECOPY)  => Gextcode +Word Gcopy                                 // INCORRECT
    rule #gas(LOG(N))       => Glog +Word (N *Word Glogdata)                        // INCORRECT
    rule #gas(OP)           => #gasCALL                      requires OP in Wcall   // INCORRECT
    rule #gas(SELFDESTRUCT) => #gasSELFDESTRUCT                                     // INCORRECT
    rule #gas(CREATE)       => Gcreate
    rule #gas(SHA3)         => Gsha3                                                // INCORRECT
    rule #gas(JUMPDEST)     => Gjumpdest
    rule #gas(SLOAD)        => Gsload
    rule #gas(OP)           => Gzero                         requires OP in Wzero
    rule #gas(OP)           => Gbase                         requires OP in Wbase
    rule #gas(OP)           => Gverylow                      requires OP in Wverylow
    rule #gas(OP)           => Glow                          requires OP in Wlow
    rule #gas(OP)           => Gmid                          requires OP in Wmid
    rule #gas(OP)           => Ghigh                         requires OP in Whigh
    rule #gas(OP)           => Gextcode                      requires OP in Wextcode
    rule #gas(BALANCE)      => Gbalance
    rule #gas(BLOCKHASH)    => Gblockhash
endmodule
```
