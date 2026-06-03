requires "verification.k"

module EVM-INT-SIMPLIFICATIONS-SPEC
    imports VERIFICATION

 // up/Int
 // ------

    claim [upInt-01]: <k> runLemma ( ((X up/Int Y) *Int Y) <Int X +Int Z )
                           => doneLemma ( true ) ... </k>
                          requires 0 <Int Y andBool Y <=Int Z

    claim [upInt-refl-lt]: <k> runLemma ( ((X up/Int Y) *Int Y) <Int X )
                            => doneLemma ( false ) ... </k>
                           requires 0 <Int Y

 // chop simplification
 // -------------------

    claim <k> runLemma ( chop( #lookup(M, KEY)   ) ) => doneLemma( #lookup(M, KEY) ) ... </k>
    claim <k> runLemma ( chop( bool2Word(B:Bool) ) ) => doneLemma( bool2Word(B)    ) ... </k>

    claim [chop-chop]: <k> runLemma ( chop( chop ( X ) ) ) => doneLemma( chop ( X ) ) ... </k>

    claim [chop-range-inferred]: <k> runLemma(X <Int chop(X *Int Y) /Int 1000000000000000000) => doneLemma(X <Int (X *Int Y) /Int 1000000000000000000) ... </k>
      requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool Y <=Int maxUInt256 /Int X

    claim [chop-notMaxUInt5]:
      <k> runLemma (
            ( notBool ( notBool ( chop ( ( chop ( ( ( notMaxUInt5 &Int ( ( notMaxUInt5 &Int ( lengthBytes ( B:Bytes ) +Int maxUInt5 ) ) +Int 95 ) ) +Int 128 ) ) +Int ( notMaxUInt5 &Int ( ( notMaxUInt5 &Int ( lengthBytes ( B:Bytes ) +Int maxUInt5 ) ) +Int 63 ) ) ) ) <Int chop ( ( ( notMaxUInt5 &Int ( ( notMaxUInt5 &Int ( lengthBytes ( B:Bytes ) +Int maxUInt5 ) ) +Int 95 ) ) +Int 128 ) ) ) ) )
          ) => doneLemma (
            false
          ) ... </k>
      requires lengthBytes(B) <Int 2 ^Int 64

    claim [chop-additional-knowledge]: <k> runLemma (
                      X <=Int chop ( X +Int C ) andBool Y <=Int chop ( Y +Int C )
              andBool notBool ( ( X +Int C <Int pow256 ) andBool ( Y +Int C <Int pow256 ) )
          ) => doneLemma ( false ) ... </k>
    requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool #rangeUInt(256, C)

    claim [chop-sub-01]: <k> runLemma ( chop ( X -Int Y ) ) => doneLemma ( X -Int Y ) ... </k>
      requires #rangeUInt(256, X) andBool #rangeUInt(256, Y) andBool Y <=Int X

    claim [chop-mul-01]: <k> runLemma ( chop ( X *Int Y ) ) => doneLemma ( X *Int Y ) ... </k>
      requires 0 <=Int X andBool X <Int 2 ^Int 96
       andBool 0 <=Int Y andBool Y <Int 2 ^Int ( 256 -Int 96 )

    claim [chop-add-sub-conc]: <k> runLemma ( chop ( 0 -Int chop ( X +Int (-16)) ) ==Int 0 ) => doneLemma ( false ) ... </k>
      requires 0 <=Int X andBool X <Int 10

    claim [chop-overflow-01]: <k> runLemma ( X:Int <=Int chop ( X +Int Y:Int ) ) => doneLemma ( true ) ... </k>
      requires #rangeUInt(128, X) andBool #rangeUInt(128, Y)

    claim [chop-overflow-02]: <k> runLemma ( X:Int <=Int chop ( X *Int Y:Int ) /Int Y ) => doneLemma ( true ) ... </k>
      requires #rangeUInt(128, X) andBool #rangeUInt(128, Y)

    claim [chop-overflow-03]: <k> runLemma ( X:Int ==Int chop ( X *Int Y:Int ) /Int Y ) => doneLemma ( false ) ... </k>
      requires pow128 <=Int X andBool X <Int pow256 andBool pow256 <=Int Y

endmodule
