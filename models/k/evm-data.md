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
                  | "chop" "(" Int ")"       [strict]
                  | "bool2Word" "(" Bool ")" [strict]
                  | Word "+Word" Word        [strict]
                  | Word "-Word" Word        [strict]
                  | Word "*Word" Word        [strict]
                  | Word "/Word" Word        [strict]
                  | Word "^Word" Word        [strict]
                  | Word "<Word" Word        [strict]
                  | Word ">Word" Word        [strict]
                  | Word "==Word" Word       [strict]

    syntax KResult ::= Int

    rule chop( I:Int ) => I                           requires I <Int (2 ^Int 256) andBool I >=Int 0
    rule chop( I:Int ) => chop( I +Int (2 ^Int 256) ) requires I <Int 0
    rule chop( I:Int ) => chop( I -Int (2 ^Int 256) ) requires I >=Int (2 ^Int 256)

    rule bool2Word(true)  => 1
    rule bool2Word(false) => 0

    rule W1:Int +Word W2:Int => chop( W1 +Int W2 )
    rule W1:Int -Word W2:Int => chop( W1 -Int W2 )
    rule W1:Int *Word W2:Int => chop( W1 *Int W2 )
    rule W1:Int /Word W2:Int => chop( W1 /Int W2 )
    rule W1:Int ^Word W2:Int => chop( W1 ^Int W2 )
    rule W1:Int <Word W2:Int => bool2Word( W1 <Int W2 )
    rule W1:Int >Word W2:Int => bool2Word( W1 >Int W2 )
    rule W1:Int ==Word W2:Int => bool2Word( W1 ==Int W2)
endmodule
```
