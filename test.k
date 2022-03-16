module TEST
    imports INT
    imports BOOL

    configuration <test> <k> $PGM:Pgm </k> </test>

    syntax Pgm ::= "SPLIT" Int
                 | "END"   Int
    rule <k> SPLIT I => END 1 ... </k> requires I ==Int 0
    rule <k> SPLIT I => END 2 ... </k> requires I =/=Int 0

    syntax Int ::= bool2Word ( Bool ) [function, functional, smtlib(bool2Word)]
    rule bool2Word( B:Bool ) => 1 requires B
    rule bool2Word( B:Bool ) => 0 requires notBool B

endmodule
