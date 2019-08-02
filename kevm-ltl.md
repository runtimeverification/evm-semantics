```k
requires "evm.k"

module LTL
    imports BOOL
    imports SET
    imports LIST

    configuration
      <ltl>
        <formula> $LTLFORMULA:LTLFormula </formula>
        <events> .Set </events>
        <trace> .List </trace>
      </ltl>

    syntax KItem ::= LTLFormula
 // ---------------------------

    syntax LTLFormula ::= LTLderive ( LTLFormula , Set ) [function]
 // ---------------------------------------------------------------

    syntax LTLEvent
 // ---------------

    syntax LTLAtom ::= "True"
                     | "False"
 // --------------------------
    rule LTLderive(LTLA:LTLAtom, _) => LTLA

    syntax LTLFormula ::= "(" LTLFormula ")" [bracket]
                        | LTLAtom
                        | LTLEvent
 // ------------------------------
    rule LTLderive(E:LTLEvent, ES) => True  requires         E in ES
    rule LTLderive(E:LTLEvent, ES) => False requires notBool E in ES

    syntax LTLFormula ::= "~" LTLFormula
                        | LTLFormula "\\/" LTLFormula
                        | LTLFormula "/\\" LTLFormula
                        | LTLFormula "->"  LTLFormula
 // -------------------------------------------------
    rule ~ True  => False [anywhere]
    rule ~ False => True  [anywhere]

    rule True  \/ FORM2 => True [anywhere]
    rule FORM1 \/ True  => True [anywhere]

    rule False \/ FORM2 => FORM2 [anywhere]
    rule FORM1 \/ False => FORM1 [anywhere]

    rule True  /\ FORM2 => FORM2 [anywhere]
    rule FORM1 /\ True  => FORM1 [anywhere]

    rule False /\ FORM2 => False [anywhere]
    rule FORM1 /\ False => False [anywhere]

    rule True  -> FORM2 => FORM2 [anywhere]
    rule FORM1 -> True  => True  [anywhere]

    rule False -> FORM2 => True    [anywhere]
    rule FORM1 -> False => ~ FORM1 [anywhere]

    rule LTLderive(~ FORM         , ES) => ~ LTLderive(FORM, ES)
    rule LTLderive(FORM1 \/ FORM2 , ES) => LTLderive(FORM1, ES) \/ LTLderive(FORM2, ES)
    rule LTLderive(FORM1 /\ FORM2 , ES) => LTLderive(FORM1, ES) /\ LTLderive(FORM2, ES)

    syntax LTLFormula ::= "EG" LTLFormula
                        | "AG" LTLFormula
 // -------------------------------------
    rule LTLderive(EG FORM, ES) => LTLderive(FORM, ES) \/ EG FORM
    rule LTLderive(AG FORM, ES) => LTLderive(FORM, ES) /\ AG FORM
endmodule

module KEVM-LTL
    imports EVM
    imports LTL

    configuration
      <kevm-ltl>
        <kevm/>
        <ltl/>
      </kevm-ltl>

    syntax EthereumSimulation ::= EthereumCommand | EthereumCommand EthereumSimulation
 // ----------------------------------------------------------------------------------
    rule <k> ETC:EthereumCommand ETS:EthereumSimulation => ETC ~> ETS ... </k>

    syntax JSON ::= OpCodes | Int
 // -----------------------------

    syntax EthereumCommand ::= "load" JSON | "start"
 // ------------------------------------------------
    rule <k> load { "gas" : GAVAIL , "code" : OPS:OpCodes , .JSONList } => . ... </k>
         <gas> _ => GAVAIL </gas>
         <program> _ => #asMapOpCodes(OPS) </program>

    rule <k> start => #execute ... </k>

    syntax OpCodes ::= UNSAFEADD ( Int , Int ) [function]
                     |   SAFEADD ( Int , Int ) [function]
 // -----------------------------------------------------
    rule UNSAFEADD(X, Y) => PUSH(32, X) ; PUSH(32, Y) ; ADD ; .OpCodes
    rule   SAFEADD(X, Y) => PUSH(32, X) ; PUSH(32, Y) ; ADD ; PUSH(32, 0) ; MSTORE         // add
                          ; PUSH(32, X) ; PUSH(32, 0) ; MLOAD ; GT ; PUSH(32, 372) ; JUMPI // check overflow
                          ; PUSH(32, Y) ; PUSH(32, 0) ; MLOAD ; GT ; PUSH(32, 372) ; JUMPI // check overflow
                          ; PUSH(32, 0) ; PUSH(32, 0) ; REVERT                             // revert
                          ; JUMPDEST ; PUSH(32, 0) ; MLOAD ; .OpCodes                      // no revert

    rule <k> #halt ~> (#execute => .) ... </k>
         <formula> FORM => LTLderive(FORM, EVENTS) </formula>
         <events> EVENTS => .Set </events>
         <trace> TRACE:List (.List => ListItem(EVENTS)) </trace>
      [priority(24)]

    rule <k> (. => #next [ OP ]) ~> #execute ... </k>
         <pc> PCOUNT </pc>
         <program> ... PCOUNT |-> OP ... </program>
         <formula> FORM => LTLderive(FORM, EVENTS) </formula>
         <events> EVENTS => .Set </events>
         <trace> TRACE:List (.List => ListItem(EVENTS)) </trace>
      [priority(24)]

    syntax LTLEvent ::= "overflow"
 // ------------------------------
    rule <k> ADD W0 W1 ... </k>
         <events> EVENTS (.Set => SetItem(overflow)) </events>
      requires notBool overflow in EVENTS
       andBool W0 +Word W1 =/=Int W0 +Int W1
      [priority(24)]

    syntax LTLEvent ::= "revert"
 // ----------------------------
    rule <k> REVERT _ _ ... </k>
         <events> EVENTS (.Set => SetItem(revert)) </events>
      requires notBool revert in EVENTS
      [priority(24)]
endmodule
```
