---
title: Data Used for EVM Execution
geometry: margin=2.5cm
...


Words
=====

Words are 256 bit integers. If you want to perform arithmetic on words, make
sure that you use the corresponding `opWord` operators (eg. `+Word`), which will
make sure the correct width is produced.

None of the rules defined here should be sensitive to any other parts of the
configuration, they should be standalone and operate at the top of the K cell.

```k
module EVM-WORD
    syntax Word ::= Int
                  | "chop" "(" Int ")"                      [strict]
                  | "bool2Word" "(" Bool ")"                [strict]
                  | Word "+Word" Word                       [strict]
                  | Word "*Word" Word                       [strict]
                  | Word "-Word" Word                       [strict]
                  | Word "/Word" Word                       [strict]
                  | Word "^Word" Word                       [strict]
                  | Word "%Word" Word                       [strict] // needs implemented
                  | "signextend" "(" Word "," Word ")"      [strict] // needs implemented
                  | Word "<Word" Word                       [strict]
                  | Word ">Word" Word                       [strict]
                  | Word "==Word" Word                      [strict]
                  | "bitwisenot" "(" Word ")"               [strict] // needs implemented
                  | "sdiv" "(" Word "," Word ")"            [strict] // needs implemented
                  | "smod" "(" Word "," Word ")"            [strict] // needs implemented
                  | "slt" "(" Word "," Word ")"             [strict] // needs implemented
                  | "sgt" "(" Word "," Word ")"             [strict] // needs implemented
                  | "bitwiseand" "(" Word "," Word ")"      [strict] // needs implemented
                  | "bitwiseor" "(" Word "," Word ")"       [strict] // needs implemented
                  | "bitwisexor" "(" Word "," Word ")"      [strict] // needs implemented
                  | "getbyte" "(" Word "," Word ")"         [strict] // needs implemented
                  | "sha3" "(" Word "," Word ")"            [strict] // needs implemented
                  | "addmod" "(" Word "," Word "," Word ")" [strict] // needs implemented
                  | "mulmod" "(" Word "," Word "," Word ")" [strict] // needs implemented

    rule chop( I:Int ) => I                           requires I <Int (2 ^Int 256) andBool I >=Int 0
    rule chop( I:Int ) => chop( I +Int (2 ^Int 256) ) requires I <Int 0
    rule chop( I:Int ) => chop( I -Int (2 ^Int 256) ) requires I >=Int (2 ^Int 256)

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
endmodule
```
