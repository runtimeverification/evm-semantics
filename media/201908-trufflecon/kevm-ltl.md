```k
requires "evm.k"

module LTL
    imports BOOL
    imports SET
    imports LIST

    configuration
      <ltl>
        <formula> $LTLFORMULA:LTLFormula </formula>
        <eventsId> .EventId </eventsId>
        <events> .Set </events>
        <trace> .List </trace>
      </ltl>

    syntax EventId ::= ".EventId"
 // -----------------------------

    syntax KItem ::= EventId "{" Set "}"
 // ------------------------------------

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

    rule LTLderive(~ FORM         , ES) => ~ LTLderive(FORM, ES)
    rule LTLderive(FORM1 \/ FORM2 , ES) => LTLderive(FORM1, ES) \/ LTLderive(FORM2, ES)
    rule LTLderive(FORM1 /\ FORM2 , ES) => LTLderive(FORM1, ES) /\ LTLderive(FORM2, ES)

    syntax LTLFormula ::= LTLFormula "->" LTLFormula [macro]
 // --------------------------------------------------------
    rule FORM1 -> FORM2 => (~ FORM1) \/ FORM2

    syntax LTLFormula ::= "always"     LTLFormula
                        | "eventually" LTLFormula
 // ---------------------------------------------
    rule LTLderive(always     FORM, ES) => LTLderive(FORM, ES) /\ always     FORM
    rule LTLderive(eventually FORM, ES) => LTLderive(FORM, ES) \/ eventually FORM

    syntax LTLFormula ::= LTLterminate ( LTLFormula ) [function]
 // ------------------------------------------------------------
    rule LTLterminate(~ FORM1)        => ~ LTLterminate(FORM1)
    rule LTLterminate(FORM1 /\ FORM2) => LTLterminate(FORM1) /\ LTLterminate(FORM2)
    rule LTLterminate(FORM1 \/ FORM2) => LTLterminate(FORM1) \/ LTLterminate(FORM2)

    rule LTLterminate(always _)     => True
    rule LTLterminate(eventually _) => False
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
         <exit-code> _ => 0 </exit-code>

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

    syntax EventId ::= Int
 // ----------------------
    rule <k> #execute ... </k>
         <pc> PCOUNT </pc>
         <formula> FORM => LTLderive(FORM, EVENTS) </formula>
         <eventsId> EID => PCOUNT </eventsId>
         <events> EVENTS => .Set </events>
         <trace> TRACE:List (.List => ListItem(EID { EVENTS })) </trace>
      requires EID =/=K PCOUNT
      [priority(24)]

    rule <k> #halt </k>
         <formula> FORM => LTLderive(FORM, EVENTS) </formula>
         <eventsId> EID => .EventId </eventsId>
         <events> EVENTS => .Set </events>
         <trace> TRACE:List (.List => ListItem(EID { EVENTS })) </trace>
      requires EID =/=K .EventId
      [priority(24)]

    rule <k> #halt </k>
         <formula> FORM => LTLterminate(FORM) </formula>
         <eventsId> .EventId </eventsId>
      requires notBool isLTLAtom(FORM)

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

    syntax LTLEvent ::= "invalid"
 // -----------------------------
    rule <k> INVALID ... </k>
         <events> EVENTS (.Set => SetItem(invalid)) </events>
      requires notBool invalid in EVENTS
      [priority(24)]
endmodule
```
