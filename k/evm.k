// EVM Semantics
// =============


requires "execution.k"
requires "world-state.k"


// We need to define the configuration before defining the semantics of any rules
// which span multiple cells.


module EVM
    imports EVM-WORLD-STATE-INTERFACE
    imports EVM-EXECUTION

    configuration <id> .AcctID </id>
                  <callStack> .CallStack </callStack>
                  initEvmCell
                  initWorldStateCell(Init)

    syntax Process ::= "{" AcctID "|" Word "|" Word "|" Word "|" WordStack "|" Map "}"
    syntax CallStack ::= ".CallStack"
                       | Process CallStack

    syntax KItem ::= "#pushCallStack"
 // ---------------------------------
    rule <k> #pushCallStack => . </k>
         <id> ACCT </id>
         <pc> PCOUNT </pc>
         <gas> GAVAIL </gas>
         <gasPrice> GPRICE </gasPrice>
         <wordStack> WS </wordStack>
         <localMem> LM </localMem>
         <callStack> CS => { ACCT | PCOUNT | GAVAIL | GPRICE | WS | LM } CS </callStack>

    syntax KItem ::= "#popCallStack"
 // --------------------------------
    rule <k> #popCallStack => . </k>
         <id> _ => ACCT </id>
         <pc> _ => PCOUNT </pc>
         <gas> _ => GAVAIL </gas>
         <gasPrice> _ => GPRICE </gasPrice>
         <wordStack> _ => WS </wordStack>
         <localMem> _ => LM </localMem>
         <callStack> { ACCT | PCOUNT | GAVAIL | GPRICE | WS | LM } CS => CS </callStack>
endmodule

