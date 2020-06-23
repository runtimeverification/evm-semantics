requires "../lemmas.k"

module VERIFICATION
    imports LEMMAS

    syntax StepSort ::= Map | ByteArray | Int
 // -----------------------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module LEMMAS-SPEC
    imports VERIFICATION

 // Buffer write simplifications
 // ----------------------------

    // rule <k> runLemma ( M [ L := .ByteArray ] [ N := WS:ByteArray ]                             ) => doneLemma ( M [ N := WS ]                        ) ... </k> requires L <=Int N
    // rule <k> runLemma ( M [ L := WS:ByteArray ] [ N := .ByteArray ]                             ) => doneLemma ( M [ L := WS ]                        ) ... </k> requires N <=Int L
    // rule <k> runLemma ( M [ 32 := (0 : 1 : 2 : .ByteArray) ] [ 32 := (3 : 4 : 5 : .ByteArray) ] ) => doneLemma ( M [ 32 := (3 : 4 : 5 : .ByteArray) ] ) ... </k>

 // #lookup simplifications
 // -----------------------

    rule <k> runLemma ( #lookupMemory((KEY |-> 33) (KEY' |-> 728) (KEY'' |-> (pow256 +Int 5)) (KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>
    rule <k> runLemma ( #lookupMemory((KEY |-> 33) (KEY' |-> 728) (KEY'' |-> (pow256 +Int 5)) (KEY''' |-> "hello"), KEY')   ) => doneLemma ( 216 ) ... </k>
    rule <k> runLemma ( #lookupMemory((KEY |-> 33) (KEY' |-> 728) (KEY'' |-> (pow256 +Int 5)) (KEY''' |-> "hello"), KEY'')  ) => doneLemma ( 5   ) ... </k>
    rule <k> runLemma ( #lookupMemory((KEY |-> 33) (KEY' |-> 728) (KEY'' |-> (pow256 +Int 5)) (KEY''' |-> "hello"), KEY''') ) => doneLemma ( 0   ) ... </k>

    rule <k> runLemma ( #lookup((KEY |-> 33) (KEY' |-> 728) (KEY'' |-> (pow256 +Int 5)) (KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>
    rule <k> runLemma ( #lookup((KEY |-> 33) (KEY' |-> 728) (KEY'' |-> (pow256 +Int 5)) (KEY''' |-> "hello"), KEY')   ) => doneLemma ( 728 ) ... </k>
    rule <k> runLemma ( #lookup((KEY |-> 33) (KEY' |-> 728) (KEY'' |-> (pow256 +Int 5)) (KEY''' |-> "hello"), KEY'')  ) => doneLemma ( 5   ) ... </k>
    rule <k> runLemma ( #lookup((KEY |-> 33) (KEY' |-> 728) (KEY'' |-> (pow256 +Int 5)) (KEY''' |-> "hello"), KEY''') ) => doneLemma ( 0   ) ... </k>

 // #range selection operation
 // --------------------------

    // Non-positive range
    rule <k> runLemma ( #range(M, N,  0) ) => doneLemma ( .ByteArray ) ... </k>
    rule <k> runLemma ( #range(M, N, -3) ) => doneLemma ( .ByteArray ) ... </k>

    // Range outside of previous buffer write
    rule <k> runLemma ( #range(M [ 32 := BUF:ByteArray ], 20, 4) ) => doneLemma ( #range(M, 20, 4) ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := BUF:ByteArray ], 48, 4) ) => doneLemma ( #range(M, 48, 4) ) ... </k> requires #sizeByteArray(BUF) <=Int 12
    rule <k> runLemma ( #range(M [ 32 := BUF:ByteArray ], 31, 1) ) => doneLemma ( #range(M, 31, 1) ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ], 33, 1) )  => doneLemma ( #range(M, 33, 1) ) ... </k>

    // Range starting before buffer write
    rule <k> runLemma ( #range(M [ 32 := BUF:ByteArray ]            , 30 , 8) ) => doneLemma ( #range(M, 30, 2) ++ (BUF [ 0 .. 6 ])                             ) ... </k> requires #sizeByteArray(BUF) >=Int 6
    rule <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : .ByteArray) ] , 30 , 8) ) => doneLemma ( #range(M, 30, 2) ++ (0 : 1 : 2 : .ByteArray) ++ #range(M, 35, 3) ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := #buf(2, BUF) ]             , 31 , 2) ) => doneLemma ( #range(M, 31, 1) ++ (#buf(2, BUF) [ 0 .. 1 ])                    ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ]             , 31 , 2) ) => doneLemma ( #range(M, 31, 1) ++ #buf(1, BUF)                                 ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ]             , 31 , 3) ) => doneLemma ( #range(M, 31, 1) ++ #buf(1, BUF) ++ #range(M, 33, 1)             ) ... </k>

    // Range starting at same point as buffer write
    rule <k> runLemma ( #range(M [ 32 := BUF:ByteArray ]            , 32 , 7) ) => doneLemma( BUF [ 0 .. 7 ]                               ) ... </k> requires #sizeByteArray(BUF) >=Int 7
    rule <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : .ByteArray) ] , 32 , 7) ) => doneLemma( (0 : 1 : 2 : .ByteArray) ++ #range(M, 35, 4) ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := #buf(2, BUF) ]             , 32 , 1) ) => doneLemma( #buf(2, BUF) [ 0 .. 1 ]                      ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ]             , 32 , 1) ) => doneLemma( #buf(1, BUF)                                 ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ]             , 32 , 2) ) => doneLemma( #buf(1, BUF) ++ #range(M, 33, 1)             ) ... </k>

    // Range starting in the middle of the buffer write
    rule <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : 3 : 4 : .ByteArray) ] , 35 , 2) ) => doneLemma( (3 : 4 : .ByteArray)                      ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : 3 : 4 : .ByteArray) ] , 35 , 8) ) => doneLemma( (3 : 4 : .ByteArray) ++ #range(M, 37, 6)  ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : .ByteArray)         ] , 33 , 1) ) => doneLemma( (1 : .ByteArray)                          ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : .ByteArray)         ] , 33 , 2) ) => doneLemma( (1 : 2 : .ByteArray)                      ) ... </k>
    rule <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : .ByteArray)         ] , 33 , 3) ) => doneLemma( (1 : 2 :  .ByteArray) ++ #range(M, 35, 1) ) ... </k>

endmodule
