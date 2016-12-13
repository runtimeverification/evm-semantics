Words
=====

Words are 256 bit integers. If you want to perform arithmetic on words, make
sure that you use the corresponding `opWord` operators (eg. `+Word`), which will
make sure the correct width is produced.

None of the rules defined here should be sensitive to any other parts of the
configuration, they should be standalone and operate at the top of the K cell.

```k
module EVM-WORD

    syntax KResult ::= Int 

    syntax Word ::= Int
                  | "#symbolicWord"
                  | "chop" "(" Int ")"                      [function]
                  | "bool2Word" "(" Bool ")"                [function]
                  | Word "+Word" Word                       [function]
                  | Word "*Word" Word                       [function]
                  | Word "-Word" Word                       [function]
                  | Word "/Word" Word                       [function]
                  | Word "^Word" Word                       [function]
                  | Word "%Word" Word                       [function]
                  | "signextend" "(" Word "," Word ")"      [function] // needs implemented
                  | Word "<Word" Word                       [function]
                  | Word ">Word" Word                       [function]
                  | Word "==Word" Word                      [function]
                  | "bitwisenot" "(" Word ")"               [function] // needs implemented
                  | "sdiv" "(" Word "," Word ")"            [function] // needs implemented
                  | "smod" "(" Word "," Word ")"            [function] // needs implemented
                  | "slt" "(" Word "," Word ")"             [function] // needs implemented
                  | "sgt" "(" Word "," Word ")"             [function] // needs implemented
                  | "bitwiseand" "(" Word "," Word ")"      [function] // needs implemented
                  | "bitwiseor" "(" Word "," Word ")"       [function] // needs implemented
                  | "bitwisexor" "(" Word "," Word ")"      [function] // needs implemented
                  | "getbyte" "(" Word "," Word ")"         [function] // needs implemented
                  | "sha3" "(" Word "," Word ")"            [function] // needs implemented
                  | "addmod" "(" Word "," Word "," Word ")" [function]
                  | "mulmod" "(" Word "," Word "," Word ")" [function]

    rule #symbolicWord => ?X:Int

    rule chop( I:Int ) => I                           //requires I <Int (2 ^Int 256) andBool I >=Int 0
    //rule chop( I:Int ) => chop( I +Int (2 ^Int 256) ) requires I <Int 0
    //rule chop( I:Int ) => chop( I -Int (2 ^Int 256) ) requires I >=Int (2 ^Int 256)

    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    rule W0:Int +Word W1:Int => chop( W0 +Int W1 )
    rule W0:Int -Word W1:Int => chop( W0 -Int W1 )
    rule W0:Int *Word W1:Int => chop( W0 *Int W1 )
    rule W0:Int /Word W1:Int => chop( W0 /Int W1 )
    rule W0:Int ^Word W1:Int => chop( W0 ^Int W1 )
    rule W0:Int <Word W1:Int => bool2Word( W0 <Int W1 )
    rule W0:Int >Word W1:Int => bool2Word( W0 >Int W1 )
    rule W0:Int ==Word W1:Int => bool2Word( W0 ==Int W1)
    rule W0:Int %Word W1:Int => chop( W0 %Int W1 )

    rule addmod(W0:Int, W1:Int, 0)      => 0
    rule addmod(W0:Int, W1:Int, W2:Int) => chop((W0 +Int W1) %Int W2) [owise]

    rule mulmod(W0:Int, W1:Int, 0)      => 0
    rule mulmod(W0:Int, W1:Int, W2:Int) => chop((W0 *Int W1) %Int W2) [owise]

    syntax WordStack ::= ".WordStack"
                       | Word ":" WordStack
    syntax Word ::= WordStack "[" Int "]" [function]

    rule (W0 : WS)[0] => W0
    rule (W0 : WS)[N] => WS[N -Int 1] requires N >Int 0

    syntax Int ::= "#stackSize" WordStack [function]

    rule #stackSize .WordStack => 0
    rule #stackSize (W : WS)   => 1 +Int (#stackSize WS)

    syntax WordList ::= List{Word, ","}
                      | "#take" "(" Int "," WordList ")" [function]
                      | "#range" "(" WordMap "," Int "," Int ")" [function]

    rule #take(0, WL)            => .WordList
    rule #take(N, (W:Word , WL)) => W , #take(N -Int 1, WL) requires N >Int 0

    rule #range(LM,         N, M) => .WordList                   requires M ==Int 0
    rule #range(N |-> W LM, N, M) => W , #range(LM, N +Int 1, M -Int 1) requires M >Int 0

    syntax WordMap ::= Map
                     | ".WordMap"
                     | WordMap "[" Int ":=" WordList "]" [function]
                     | "#asMap" "(" WordList ")"         [function]

    rule .WordMap => .Map [macro]

    rule LM[N := .WordList]    => LM
    rule LM[N := W0:Word , WL] => (LM[N <- W0])[N +Int 1 := WL]

    rule #asMap(.WordList) => .Map
    rule #asMap(WL) => (0 |-> 0)[0 := WL] requires WL =/=K .WordList

endmodule
```
