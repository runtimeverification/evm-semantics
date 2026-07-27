requires "verification.k"

module LEMMAS-SPEC
    imports VERIFICATION

 // Addresses
 // ---------

    // claim [newaddr.compare]: <k> runLemma(#isPrecompiledAccount(#newAddr(TESTER_ACCT, 1), ISTANBUL)) => doneLemma(false) ... </k> requires #rangeAddress(TESTER_ACCT)

 // Arithmetic
 // ----------

    claim <k> runLemma(#rangeUInt(256, #lookup(M, KX) -Int #lookup(M, KY))) => doneLemma(true) ... </k>
      requires #rangeUInt(256, X) andBool X ==Int #lookup(M,  KX)
       andBool #rangeUInt(256, Y) andBool Y ==Int #lookup(M,  KY)
       andBool #rangeUInt(256, Z) andBool Z ==Int #lookup(M, _KZ)
       andBool #rangeUInt(256, (X -Int Y) -Int Z)

    claim [buf-shift]:
      <k> runLemma (
            #buf ( 20, X <<Int 16 )
          ) => doneLemma (
            #buf ( 18 , X:Int ) +Bytes b"\x00\x00"
          ) ... </k>
          requires 0 <=Int X andBool X <Int 2 ^Int 144

 // Sets
 // ----

    claim [set-union-01]:
      <k> runLemma (
            notBool ( ( ((((S:Set |Set SetItem(X)) |Set SetItem (X)) |Set SetItem(Y)) |Set SetItem(X))
                          ==K
                          ((S:Set |Set SetItem(X)) |Set SetItem (Y))
                      ) ==Bool false
                    ) ==Bool true
          ) =>
          doneLemma (
            true
          ) ...
      </k>
      requires X =/=K Y

// List simplifications
// --------------------

  claim [list-in-simplification]:
    <k> runLemma ( b"\xd3V\x97\x17" in ListItem ( b"Y\xecK\x01" +Bytes #buf ( 32 , W:Int ) ) ) => doneLemma ( false ) ... </k>
      requires #rangeUInt(256, W)

 // #lookup simplifications
 // -----------------------

    claim <k> runLemma ( #lookupMemory(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) ( KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY')   ) => doneLemma ( 216 ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) (_KEY' |-> 728) ( KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY'')  ) => doneLemma ( 5   ) ... </k>
    claim <k> runLemma ( #lookupMemory((_KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) ( KEY''' |-> "hello"), KEY''') ) => doneLemma ( 0   ) ... </k>
    //TODO Haskell limitation? https://github.com/runtimeverification/haskell-backend/issues/1948
    //claim <k> runLemma ( #lookupMemory((KEY |-> 33), KEY') ) => doneLemma ( 0 ) ... </k> requires notBool KEY' in_keys(KEY |-> 33)

    claim <k> runLemma ( #lookup(( KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY)    ) => doneLemma ( 33  ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) ( KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY')   ) => doneLemma ( 728 ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) (_KEY' |-> 728) ( KEY'' |-> (pow256 +Int 5)) (_KEY''' |-> "hello"), KEY'')  ) => doneLemma ( 5   ) ... </k>
    claim <k> runLemma ( #lookup((_KEY |-> 33) (_KEY' |-> 728) (_KEY'' |-> (pow256 +Int 5)) ( KEY''' |-> "hello"), KEY''') ) => doneLemma ( 0   ) ... </k>
    //claim <k> runLemma ( #lookup((KEY |-> 33), KEY') ) => doneLemma ( 0 ) ... </k> requires notBool KEY' in_keys(KEY |-> 33)

    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY    ) ) => doneLemma ( 33  ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY'   ) ) => doneLemma ( 728 ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''  ) ) => doneLemma ( 5   ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''
    claim <k> runLemma ( #lookup( _M:Map [ KEY <- 33 ] [ KEY' <- 728 ] [ KEY'' <- (pow256 +Int 5) ] [ KEY''' <- "hello" ] , KEY''' ) ) => doneLemma ( 0   ) ... </k> requires KEY =/=Int KEY' andBool KEY =/=Int KEY'' andBool KEY =/=Int KEY''' andBool KEY' =/=Int KEY'' andBool KEY' =/=Int KEY''' andBool KEY'' =/=Int KEY'''

    claim [lookup-key-neq]: <k> runLemma ( #lookup( ( (3 |-> 3) (5 |-> 5) (7 |-> 7) M:Map ) [ 9 <- 9 ] [ 11 <- 11 ] [ 13 <- 13 ], KEY ) ) => doneLemma ( #lookup (M, KEY) ) ... </k> requires 15 <=Int KEY

// Symbolic bytes lookup simplification
// -------------------
    claim [lookup-symbolic-bytes]: 
      <k> runLemma ( b"`\xa0`@R4\x80\x15a\x00\x10W`\x00" +Bytes #buf ( 32 , W:Int )  [ 0 ] )
        => doneLemma ( 96 ) ... </k>
        requires #rangeUInt(256, W)

 // #buf simplification
 // -------------------
    claim [bufExtractPadding]: <k> runLemma ( #asWord ( ( #range( #buf ( 32 , X ), 0, 28 ) ):Bytes ) ) => doneLemma ( 0 ) ... </k> requires #rangeUInt(32, X)

    claim <k> runLemma ( #buf( 32 , bool2Word ( B:Bool ) ) ==K #buf( 32 , 1 )     ) => doneLemma( B ==K true ) ... </k>
    claim <k> runLemma ( #buf( 32 , I:Int )                ==K #buf( 32 , 1 )     ) => doneLemma( I ==K 1    ) ... </k> requires #rangeUInt(256, I)
    claim <k> runLemma ( #buf( 32 , 1 )                    ==K #buf( 32 , I:Int ) ) => doneLemma( I ==K 1    ) ... </k> requires #rangeUInt(256, I)

    claim <k> runLemma ( #bufStrict( #ceil32(LEN) -Int LEN, 0 ) ) => doneLemma( #buf( #ceil32(LEN) -Int LEN, 0 ) ) ... </k> requires 0 <=Int LEN

    claim [bufstrict-simplify]:
          <k> runLemma ( #bufStrict(32, #getValue(#int256(X))) ) => doneLemma ( #buf(32, chop(X)) ) ... </k> requires #rangeSInt(256, X)

    claim <k> runLemma( #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER         .IntList))) ) => doneLemma(#buf(32, #hashedLocation("Solidity", 2, OWNER         .IntList))) ... </k> requires #rangeUInt(256, OWNER)
    claim <k> runLemma( #padToWidth(32, #asByteStack(#hashedLocation("Solidity", 2, OWNER SPENDER .IntList))) ) => doneLemma(#buf(32, #hashedLocation("Solidity", 2, OWNER SPENDER .IntList))) ... </k> requires #rangeUInt(256, OWNER) andBool #rangeUInt(256, SPENDER)

    claim <k> runLemma( #buf(32, X +Int Y) +Bytes #buf(lengthBytes(B), 0) +Bytes #buf(32 +Int Y -Int Y, #asWord(B))) => doneLemma ( #buf(32, Z -Int Y) +Bytes #buf(32, ((3 *Int Y) -Int (2 *Int Y)) -Int Y) +Bytes B ) ... </k>
      requires lengthBytes(B) <=Int 4
       andBool 0 <=Int X andBool 0 <=Int Y andBool Y <=Int Z
       andBool X <Int 256 andBool Y <Int 256 andBool Z <Int 256
       andBool X +Int (2 *Int Y) -Int Z ==Int 0


 // #padToWidth simplification
 // --------------------------

    claim <k> runLemma ( #padToWidth( 32 , #asByteStack( bool2Word ( B:Bool ) ) ) ) => doneLemma( #buf( 32 , bool2Word ( B ) ) ) ... </k>
    claim <k> runLemma ( #padToWidth( 32 , #asByteStack( maxUInt160 &Int #newAddr(ACCT, 1) ) ) )
           => doneLemma( #buf(32, #newAddr(ACCT, 1)) ) ... </k>

    //Required for ERC20 + solc5 + constructor call
    claim <k> runLemma ( 160 ==Int #asWord ( #buf( 4, 160 ) +Bytes ( #range( #buf( 32 , _BUF ), 0, 28 ) ) ) >>Int 224 )
           => doneLemma( true ) ... </k>

 // concatenation simplification
 // ----------------------------

    claim [bytes-reassociation]: <k> runLemma  ( ((((A +Bytes B) +Bytes C) +Bytes D) +Bytes E) +Bytes F )
                                  => doneLemma ( A +Bytes (B +Bytes (C +Bytes (D +Bytes (E +Bytes F)))) ) ... </k>

 // concat
 // ------

    claim <k> runLemma ( lengthBytes ( #range ( #buf ( 32 , _X ) , 3 , 29 ) +Bytes b"\x01" +Bytes #buf ( 2 , Y ) ) )
        => doneLemma ( 32 ) ... </k>
        requires #rangeUInt ( 16 , Y )

    claim <k> runLemma ( #asWord ( #range ( #buf ( 32 , X ) , 0 , 29 ) +Bytes #range ( #buf ( 32 , X ) , 29 , 3 ) ) )
        => doneLemma ( X ) ... </k>
        requires #rangeUInt ( 256 , X )

 // #padRightToWidth
 // ----------------

    claim [pRTW-01]:
      <k> runLemma (
            notBool ( #asWord ( #padRightToWidth ( 32 , #buf ( 4 , VV0_x_114b9705:Int ) ) ) ==Int
              #asWord ( #buf ( 4 , VV0_x_114b9705:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00" ) )
          ) => doneLemma(
            false
          ) ... </k>
        requires #rangeUInt(32, VV0_x_114b9705)

 // #asWord
 // ----------------

    claim [buf-asWord-invert]:
      <k> runLemma(
            #asWord ( #buf ( 63 , lengthBytes ( VV0_data_114b9705:Bytes ) ) ) <=Int maxUInt64
          ) => doneLemma(
            true
          ) ... </k>
        requires lengthBytes ( VV0_data_114b9705:Bytes ) <=Int 1073741824

    claim [asWord-unif-01]: // two `#asWord`s, both under 32 bytes
      <k> runLemma(
            #asWord ( B1 +Bytes B2 ) ==Int #asWord ( B3 )
          ) => doneLemma(
            #buf(22, 0) +Bytes B1 +Bytes B2 ==K #buf(16, 0) +Bytes B3
          ) ... </k>
        requires lengthBytes(B1) ==Int 4 andBool lengthBytes(B2) ==Int 6
         andBool lengthBytes(B3) ==Int 16

    claim [asWord-unif-02]: // two `#asWord`s, left over 32 bytes
      <k> runLemma(
            #asWord ( B1 +Bytes B2 ) ==Int #asWord ( B3 +Bytes B4 )
          ) => doneLemma(
            #range ( B1, 7, 5 ) +Bytes B2 ==K #buf(7, 0) +Bytes B3 +Bytes B4
          ) ... </k>
        requires lengthBytes(B1) ==Int 12 andBool lengthBytes(B2) ==Int 27
         andBool lengthBytes(B3) ==Int 10 andBool lengthBytes(B4) ==Int 15

    claim [asWord-unif-03]: // `#asWord` and constant out of range, buffer length <=Int 32
      <k> runLemma(
            #asWord ( B ) ==Int -15 orBool 2 ^Int 160 ==Int #asWord ( B )
          ) => doneLemma(
            false
          ) ... </k>
          requires lengthBytes(B) ==Int 16

    claim [asWord-unif-04]: // `#asWord` and constant out of range, buffer length >Int 32
      <k> runLemma(
            #asWord ( B ) ==Int -15 orBool 2 ^Int 324 ==Int #asWord ( B )
          ) => doneLemma(
            false
          ) ... </k>
          requires lengthBytes(B) ==Int 36

    claim [asWord-unif-05]: // `#asWord` and constant, buffer length <=Int 32
      <k> runLemma(
            #asWord ( B1 +Bytes B2 ) ==Int 9518572911576893851958972884578457483927345
          ) => doneLemma(
            B1 +Bytes B2 ==K #buf(27, 9518572911576893851958972884578457483927345)
          ) ... </k>
        requires lengthBytes(B1) ==Int 15 andBool lengthBytes(B2) ==Int 12

    claim [asWord-unif-06]: // `#asWord` and constant, buffer length >Int 32
      <k> runLemma(
            #asWord ( B1 +Bytes B2 ) ==Int 294572972648782479679175618975648679836
          ) => doneLemma(
            #range(B1, 3, 17) +Bytes B2 ==K #buf(32, 294572972648782479679175618975648679836)
          ) ... </k>
        requires lengthBytes(B1) ==Int 20 andBool lengthBytes(B2) ==Int 15

    claim [asWord-chop-overflow-div]:
      <k> runLemma(
            #asWord( BA1 +Bytes BA2 ) /Int N
          ) => doneLemma(
            // #asWord ( BA2 ) /Int N
            #asWord ( #range ( BA2, 0, lengthBytes( BA2 ) -Int ( log2Int( N ) /Int 8 ) ) )
          ) ... </k>
        requires 0 <Int N andBool N ==Int 2 ^Int log2Int ( N ) andBool log2Int( N ) modInt 8 ==Int 0
         andBool 0 <Int lengthBytes(BA1) andBool lengthBytes(BA2) ==Int 32

    claim [asWord-chop-overflow-lt]:
      <k> runLemma(
            #asWord ( BA1 +Bytes BA2 +Bytes BA3 ) <Int X:Int
          ) => doneLemma(
            #asWord ( BA2 +Bytes BA3 ) <Int X
          ) ... </k>
        requires #asWord ( BA3 ) ==Int X modInt ( 2 ^Int ( 8 *Int lengthBytes ( BA3 ) ) )
         andBool 0 <Int lengthBytes(BA1) andBool lengthBytes(BA2 +Bytes BA3) ==Int 32

    claim [asWord-chop-overflow-le]:
      <k> runLemma(
            #asWord ( BA1 +Bytes BA2 +Bytes BA3 ) <=Int X:Int
          ) => doneLemma(
            #asWord ( BA2 +Bytes BA3 ) <=Int X
          ) ... </k>
        requires #asWord ( BA3 ) ==Int X modInt ( 2 ^Int ( 8 *Int lengthBytes ( BA3 ) ) )
         andBool 0 <Int lengthBytes(BA1) andBool lengthBytes(BA2 +Bytes BA3) ==Int 32

    claim [asWord-lt-concat-left]:
      <k> runLemma (
            #asWord ( B1 +Bytes b"\xde\xad\xbe\xef" ) <Int #asWord ( b"\xfa\xca\xde\x00\x00\x00\x00" )
          ) => doneLemma (
            #asWord ( B1 ) <Int #asWord ( b"\xfa\xca\xde")
          ) ... </k>

 // ecrecover
 // ---------

    claim [ecrec-length]: <k> runLemma  ( lengthBytes ( #ecrec ( _ , _ , _ , _ ) ) <=Int 32 )
                           => doneLemma ( true ) ... </k>

    claim [ecrec-split]: <k> runLemma  ( #range ( #buf(160, 0) +Bytes _BUF , lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) +Int 128 , 32 -Int lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) )
                          => doneLemma ( #range ( #buf( 32, 0)             , lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) )          , 32 -Int lengthBytes ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) ) ... </k>

    claim [ecrec-range]: <k> runLemma  ( #rangeUInt ( 160 , #asWord ( #ecrec ( _ , _ , _ , _ ) ) ) )
                          => doneLemma ( true ) ... </k>

    // claim [ecrec-mask]: <k> runLemma  ( #asWord ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) &Int maxUInt160 )
    //                      => doneLemma ( #asWord ( #ecrec ( HASH , SIGV , SIGR , SIGS ) ) ) ... </k>

 // Address computation
 // -------------------

    claim [addr-from-private-key]: <k> runLemma  ( #addrFromPrivateKey(#unparseDataBytes(b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x01")) )
                                    => doneLemma ( 721457446580647751014191829380889690493307935711 ) ... </k>

 // Precompiled accounts
 // --------------------

    claim [precompiledAccountsSet-correctness]:
          <k> runLemma (
                         #precompiledAccountsSet(DEFAULT)           ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(FRONTIER)          ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(HOMESTEAD)         ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(TANGERINE_WHISTLE) ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(SPURIOUS_DRAGON)   ==K SetItem (1) ( SetItem (2) ( SetItem (3) SetItem (4) ) )
                 andBool #precompiledAccountsSet(BYZANTIUM)         ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) SetItem (8) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(CONSTANTINOPLE)    ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) SetItem (8) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(PETERSBURG)        ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) SetItem (8) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(ISTANBUL)          ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(BERLIN)            ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(LONDON)            ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(MERGE)             ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
                 andBool #precompiledAccountsSet(SHANGHAI)          ==K SetItem (1) ( SetItem (2) ( SetItem (3) ( SetItem (4) ( SetItem (5) ( SetItem (6) ( SetItem (7) ( SetItem (8) SetItem (9) ) ) ) ) ) ) )
              ) => doneLemma ( true ) ... </k>

    claim [precompiledAccounts-slowdown]: <k> runLemma  ( X:Bool ) => doneLemma ( X:Bool ) ... </k>
      requires #isPrecompiledAccount(_A00, SHANGHAI) andBool #isPrecompiledAccount(_A01, SHANGHAI) andBool #isPrecompiledAccount(_A02, SHANGHAI) andBool #isPrecompiledAccount(_A03, SHANGHAI) andBool #isPrecompiledAccount(_A04, SHANGHAI)
       andBool #isPrecompiledAccount(_A05, SHANGHAI) andBool #isPrecompiledAccount(_A06, SHANGHAI) andBool #isPrecompiledAccount(_A07, SHANGHAI) andBool #isPrecompiledAccount(_A08, SHANGHAI) andBool #isPrecompiledAccount(_A09, SHANGHAI)
       andBool #isPrecompiledAccount(_A10, SHANGHAI) andBool #isPrecompiledAccount(_A11, SHANGHAI) andBool #isPrecompiledAccount(_A12, SHANGHAI) andBool #isPrecompiledAccount(_A13, SHANGHAI) andBool #isPrecompiledAccount(_A14, SHANGHAI)
       andBool #isPrecompiledAccount(_A15, SHANGHAI) andBool #isPrecompiledAccount(_A16, SHANGHAI) andBool #isPrecompiledAccount(_A17, SHANGHAI) andBool #isPrecompiledAccount(_A18, SHANGHAI) andBool #isPrecompiledAccount(_A19, SHANGHAI)
       andBool #isPrecompiledAccount(_A20, SHANGHAI) andBool #isPrecompiledAccount(_A21, SHANGHAI) andBool #isPrecompiledAccount(_A22, SHANGHAI) andBool #isPrecompiledAccount(_A23, SHANGHAI) andBool #isPrecompiledAccount(_A24, SHANGHAI)
       andBool #isPrecompiledAccount(_A25, SHANGHAI) andBool #isPrecompiledAccount(_A26, SHANGHAI) andBool #isPrecompiledAccount(_A27, SHANGHAI) andBool #isPrecompiledAccount(_A28, SHANGHAI) andBool #isPrecompiledAccount(_A29, SHANGHAI)
       andBool #isPrecompiledAccount(_A30, SHANGHAI) andBool #isPrecompiledAccount(_A31, SHANGHAI) andBool #isPrecompiledAccount(_A32, SHANGHAI) andBool #isPrecompiledAccount(_A33, SHANGHAI) andBool #isPrecompiledAccount(_A34, SHANGHAI)
       andBool #isPrecompiledAccount(_A35, SHANGHAI) andBool #isPrecompiledAccount(_A36, SHANGHAI) andBool #isPrecompiledAccount(_A37, SHANGHAI) andBool #isPrecompiledAccount(_A38, SHANGHAI) andBool #isPrecompiledAccount(_A39, SHANGHAI)
       andBool #isPrecompiledAccount(_A40, SHANGHAI) andBool #isPrecompiledAccount(_A41, SHANGHAI) andBool #isPrecompiledAccount(_A42, SHANGHAI) andBool #isPrecompiledAccount(_A43, SHANGHAI) andBool #isPrecompiledAccount(_A44, SHANGHAI)
       andBool #isPrecompiledAccount(_A45, SHANGHAI) andBool #isPrecompiledAccount(_A46, SHANGHAI) andBool #isPrecompiledAccount(_A47, SHANGHAI) andBool #isPrecompiledAccount(_A48, SHANGHAI) andBool #isPrecompiledAccount(_A49, SHANGHAI)

endmodule
