requires "../lemmas.k"

module VERIFICATION
    imports LEMMAS

    syntax StepSort ::= Map | ByteArray | Int | Bool
 // ------------------------------------------------

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module LEMMAS-SPEC
    imports VERIFICATION

 // bool2Word
 // ---------

    claim <k> runLemma ( bool2Word((UINT8 ==K 0) ==K false) ) => doneLemma ( UINT8 ) ... </k> requires #rangeBool(UINT8)

 // Buffer write simplifications
 // ----------------------------

    // claim <k> runLemma ( M [ L := .ByteArray ] [ N := WS:ByteArray ]                             ) => doneLemma ( M [ N := WS ]                        ) ... </k> requires L <=Int N
    // claim <k> runLemma ( M [ L := WS:ByteArray ] [ N := .ByteArray ]                             ) => doneLemma ( M [ L := WS ]                        ) ... </k> requires N <=Int L
    // claim <k> runLemma ( M [ 32 := (0 : 1 : 2 : .ByteArray) ] [ 32 := (3 : 4 : 5 : .ByteArray) ] ) => doneLemma ( M [ 32 := (3 : 4 : 5 : .ByteArray) ] ) ... </k>

    // claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I1 <- 1 ] [ I2 <- 2 ] ) ... </k> requires I1  <Int I2
    // claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I2 <- 2 ] [ I1 <- 1 ] ) ... </k> requires I1  >Int I2
    // claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I1 <- 2 ]             ) ... </k> requires I1 ==Int I2
    // claim <k> runLemma ( M:Map [ I1 <- 1 ] [ I2 <- 2 ] ) => doneLemma ( M [ I2 <- 2 ]             ) ... </k> requires I1 ==Int I2

 // #lookup simplifications
 // -----------------------

    claim <k> runLemma ( #lookupMemory(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) ( KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY')   ) => doneLemma ( 216 ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) (_KEY' |-> 728) ( KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY'')  ) => doneLemma ( 5   ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) ( KEY''' |-> "hello"), KEY''') ) => doneLemma ( 0   ) ... </k>
    //TODO Haskell limitation? https://github.com/kframework/kore/issues/1948
    //claim <k> runLemma ( #lookupMemory((KEY |-> 33), KEY') ) => doneLemma ( 0 ) ... </k> requires notBool KEY' in_keys(KEY |-> 33)

    claim <k> runLemma ( #lookup(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) ( KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY')   ) => doneLemma ( 728 ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) (_KEY' |-> 728) ( KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY'')  ) => doneLemma ( 5   ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) ( KEY''' |-> "hello"), KEY''') ) => doneLemma ( 0   ) ... </k>
    //claim <k> runLemma ( #lookup((KEY |-> 33), KEY') ) => doneLemma ( 0 ) ... </k> requires notBool KEY' in_keys(KEY |-> 33)

    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY    ) ) => doneLemma ( 33  ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY'   ) ) => doneLemma ( 728 ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    // claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''  ) ) => doneLemma ( 5   ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    // claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''' ) ) => doneLemma ( 0   ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''

 // #range selection operation
 // --------------------------

    // Non-positive range
    claim <k> runLemma ( #range(_M, _N,  0) ) => doneLemma ( .ByteArray ) ... </k>
    claim <k> runLemma ( #range(_M, _N, -3) ) => doneLemma ( .ByteArray ) ... </k>

    // Range outside of previous buffer write
    claim <k> runLemma ( #range(M [ 32 := _BUF:ByteArray ], 20, 4) ) => doneLemma ( #range(M, 20, 4) ) ... </k>
    claim <k> runLemma ( #range(M [ 32 :=  BUF:ByteArray ], 48, 4) ) => doneLemma ( #range(M, 48, 4) ) ... </k> requires #sizeByteArray(BUF) <=Int 12
    claim <k> runLemma ( #range(M [ 32 := _BUF:ByteArray ], 31, 1) ) => doneLemma ( #range(M, 31, 1) ) ... </k>
    claim <k> runLemma ( #range(M [ 32 := #buf(1, _BUF) ] , 33, 1) ) => doneLemma ( #range(M, 33, 1) ) ... </k>

    // Range starting before buffer write
    claim <k> runLemma ( #range(M [ 32 := BUF:ByteArray ]            , 30 , 8) ) => doneLemma ( #range(M, 30, 2) ++ (BUF [ 0 .. 6 ])                             ) ... </k> requires #sizeByteArray(BUF) >=Int 6
    claim <k> runLemma ( #range(M [ 32 := (0 : 1 : 2 : .ByteArray) ] , 30 , 8) ) => doneLemma ( #range(M, 30, 2) ++ (0 : 1 : 2 : .ByteArray) ++ #range(M, 35, 3) ) ... </k>
    claim <k> runLemma ( #range(M [ 32 := #buf(2, BUF) ]             , 31 , 2) ) => doneLemma ( #range(M, 31, 1) ++ (#buf(2, BUF) [ 0 .. 1 ])                    ) ... </k>
    claim <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ]             , 31 , 2) ) => doneLemma ( #range(M, 31, 1) ++ #buf(1, BUF)                                 ) ... </k>
    claim <k> runLemma ( #range(M [ 32 := #buf(1, BUF) ]             , 31 , 3) ) => doneLemma ( #range(M, 31, 1) ++ #buf(1, BUF) ++ #range(M, 33, 1)             ) ... </k>

    // Range starting at same point as buffer write
    claim <k> runLemma ( #range(_M [ 32 := BUF:ByteArray ]            , 32 , 7) ) => doneLemma( BUF [ 0 .. 7 ]                               ) ... </k> requires #sizeByteArray(BUF) >=Int 7
    claim <k> runLemma ( #range( M [ 32 := (0 : 1 : 2 : .ByteArray) ] , 32 , 7) ) => doneLemma( (0 : 1 : 2 : .ByteArray) ++ #range(M, 35, 4) ) ... </k>
    claim <k> runLemma ( #range(_M [ 32 := #buf(2, BUF) ]             , 32 , 1) ) => doneLemma( #buf(2, BUF) [ 0 .. 1 ]                      ) ... </k>
    claim <k> runLemma ( #range(_M [ 32 := #buf(1, BUF) ]             , 32 , 1) ) => doneLemma( #buf(1, BUF)                                 ) ... </k>
    claim <k> runLemma ( #range( M [ 32 := #buf(1, BUF) ]             , 32 , 2) ) => doneLemma( #buf(1, BUF) ++ #range(M, 33, 1)             ) ... </k>

    // Range starting in the middle of the buffer write
    claim <k> runLemma ( #range(_M [ 32 := (0 : 1 : 2 : 3 : 4 : .ByteArray) ] , 35 , 2) ) => doneLemma( (3 : 4 : .ByteArray)                      ) ... </k>
    claim <k> runLemma ( #range( M [ 32 := (0 : 1 : 2 : 3 : 4 : .ByteArray) ] , 35 , 8) ) => doneLemma( (3 : 4 : .ByteArray) ++ #range(M, 37, 6)  ) ... </k>
    claim <k> runLemma ( #range(_M [ 32 := (0 : 1 : 2 : .ByteArray)         ] , 33 , 1) ) => doneLemma( (1 : .ByteArray)                          ) ... </k>
    claim <k> runLemma ( #range(_M [ 32 := (0 : 1 : 2 : .ByteArray)         ] , 33 , 2) ) => doneLemma( (1 : 2 : .ByteArray)                      ) ... </k>
    claim <k> runLemma ( #range( M [ 32 := (0 : 1 : 2 : .ByteArray)         ] , 33 , 3) ) => doneLemma( (1 : 2 :  .ByteArray) ++ #range(M, 35, 1) ) ... </k>

 // #buf simplification
 // -------------------

    claim <k> runLemma ( #buf( 32 , bool2Word ( B:Bool ) ) ==K #buf( 32 , 1 )     ) => doneLemma( B ==K true ) ... </k>
    claim <k> runLemma ( #buf( 32 , I:Int )                ==K #buf( 32 , 1 )     ) => doneLemma( I ==K 1    ) ... </k>
    claim <k> runLemma ( #buf( 32 , 1 )                    ==K #buf( 32 , I:Int ) ) => doneLemma( I ==K 1    ) ... </k>

 // chop simplification
 // -------------------

    claim <k> runLemma ( chop( #lookup(M, KEY)   ) ) => doneLemma( #lookup(M, KEY) ) ... </k>
    claim <k> runLemma ( chop( bool2Word(B:Bool) ) ) => doneLemma( bool2Word(B)    ) ... </k>

 // #padToWidth simplification
 // --------------------------

    claim <k> runLemma ( #padToWidth( 32 , #asByteStack( bool2Word ( B:Bool ) ) ) ) => doneLemma( #buf( 32 , bool2Word ( B ) ) ) ... </k>
    claim <k> runLemma ( #padToWidth( 32 , #asByteStack( maxUInt160 &Int #newAddr(ACCT, 1) ) ) )
           => doneLemma( #buf(32, #newAddr(ACCT, 1)) ) ... </k>

    //Required for ERC20 + solc5 + constructor call
    claim <k> runLemma ( bool2Word ( 160 ==Int #asWord ( Int2Bytes(4, 160, BE) ++ ( #buf ( 32 , _BUF ) [ 0 .. 28 ] ) ) >>Int 224 ) )
           => doneLemma( true ) ... </k>

endmodule
