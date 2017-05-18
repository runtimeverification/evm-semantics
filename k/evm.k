// EVM Semantics
// =============


requires "execution.k"
requires "world-state.k"


// We need to define the configuration before defining the semantics of any rules
// which span multiple cells.


module EVM-CONFIGURATION
    imports EVM-WORLD-STATE-INTERFACE
    imports EVM-EXECUTION

    configuration <id> .AcctID </id>
                  <callStack> .CallStack </callStack>
                  initEvmCell
                  initWorldStateCell(Init)
endmodule


// Interprocedural Execution
// -------------------------

// Here we give the semantics to operations which communicate/call between accounts
// on the network.


module EVM
    imports EVM-CONFIGURATION

    syntax KItem ::= "#processCall" "{" AcctID "|" Word "|" WordStack "}"
 // ---------------------------------------------------------------------
    rule <k> CALL GASAMT ACCT ETHER INOFFSET INSIZE OUTOFFSET OUTSIZE
          => #processCall { ACCT | ETHER | #range(LM, INOFFSET, INSIZE) }
          ...
         </k>
         <localMem> LM </localMem>

    // TODO: How are we handling refunding unused gas?
    rule <k> #processCall {ACCT | ETHER | WL}
          =>    #pushCallStack
             ~> #setProcess {ACCT | 0 | ETHER | .WordStack | #asMap(WL)}
         ... </k>
         <id> CURRACCT </id>

    syntax KItem ::= "#processReturn" WordStack
 // -------------------------------------------
    rule #processReturn WL => #popCallStack ~> #returnValues WL
    rule <k> RETURN INIT SIZE => #processReturn #range(LM, INIT, SIZE) ... </k>
         <localMem> LM </localMem>

    syntax KItem ::= "#returnValues" WordStack
 // ------------------------------------------
    rule <k> #returnValues WL => #updateLocalMem INIT #take(SIZE, WL) ... </k>
         <wordStack> INIT : SIZE : WS => WS </wordStack>
endmodule

