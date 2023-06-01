requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bool | Int | Bytes
 // ----------------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    // Arithmetic

    claim ((X +Int pow256) -Int chop(Y)) => (X -Int Y)
      requires #rangeUInt(256, X)
       andBool #rangeSInt(256, Y)
       andBool Y <Int 0

    claim (chop(Art_i *Int (ABI_rate +Int pow256))) => (chop(Art_i *Int ABI_rate))
      requires #rangeUInt(256, Art_i)
       andBool Art_i <=Int maxSInt256
       andBool #rangeSInt(256, Art_i *Int ABI_rate)

    claim (maxUInt48 &Int ABI_x <=Int maxUInt48 &Int ABI_x +Int ABI_y) => (false)
      requires #rangeUInt(48, ABI_x)
       andBool #rangeUInt(48, ABI_y)
       andBool notBool #rangeUInt(48, ABI_x +Int ABI_y)

    claim ( (maxUInt48 &Int W1) +Int (maxUInt160 &Int W2) )
          => ( X +Int Y )
          requires (W1 ==Int #WordPackUInt48UInt48(X, _))
           andBool (W2 ==Int #WordPackAddrUInt48UInt48(Y, _, _))

    claim (bool2Word(ABI_src:Int ==Int CALLER_ID:Int) |Int bool2Word(X)) => (bool2Word(ABI_src ==Int CALLER_ID orBool X)) 
      requires #rangeUInt(256, ABI_src)
       andBool #rangeUInt(256, CALLER_ID)

    claim (bool2Word(ABI_src ==Int CALLER_ID orBool X) ==Int 0) => (notBool(ABI_src ==Int CALLER_ID orBool X)) 
      requires #rangeUInt(256, ABI_src)
       andBool #rangeUInt(256, CALLER_ID)

    claim  ( chop( A -Int B ) <=Int A  ) =>  ( false ) 
      requires #rangeUInt(256, A) andBool #rangeUInt(256, B) andBool A -Int B <Int 0

    // WordPack

    claim ((GAL |Int (notMaxUInt160 &Int GUY_TIC_END)) modInt pow256) => (GAL |Int (notMaxUInt160 &Int GUY_TIC_END)) 
      requires #rangeUInt(256, GUY_TIC_END)
       andBool #rangeAddress(GAL)

    claim (TIME +Int (TTL_TAU /Int pow48)) => (TIME +Int TAU) 
      requires TTL_TAU ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool #rangeUInt(48, TIME +Int TAU)

    claim (maxUInt48 &Int ((GAL |Int (notMaxUInt160 &Int GUY_TIC_END)) /Int pow160)) => (TIC) 
      requires GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)

    claim (maxUInt160 &Int (GAL |Int (notMaxUInt160 &Int GUY_TIC_END))) => (GAL) 
      requires GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)

    claim [wordPackSimplify1]: <k> runLemma((((TIME +Int (maxUInt48 &Int (TTL_TAU /Int pow48))) *Int pow208) |Int (maxUInt208 &Int
    (GAL |Int (notMaxUInt160 &Int GUY_TIC_END))))) => doneLemma(#WordPackAddrUInt48UInt48(GAL, TIC, TIME +Int TAU))
    ... </k>
      requires TTL_TAU     ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL)
       andBool #rangeUInt(48, TIME +Int TAU)

    claim [wordPackSimplify2]: <k> runLemma((((TIME +Int (maxUInt48 &Int TTL_TAU)) *Int pow160) |Int
    (maskWordPackAddrUInt48UInt48_2 &Int GUY_TIC_END))) => doneLemma(#WordPackAddrUInt48UInt48(GUY, TIME +Int TTL,
    END)) ... </k>
      requires TTL_TAU     ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeUInt(48, TIME +Int TTL)

    claim (maxUInt48 &Int ((CALLER_ID |Int (notMaxUInt160 &Int #lookup(M, KX))) /Int pow208)) => (maxUInt48 &Int (#lookup(M, KX) /Int pow208)) 
      requires #rangeAddress(CALLER_ID)

    claim (TIME +Int ( maxUInt48 &Int #lookup ( ACCT_ID_STORAGE [ keccak ( #buf ( 32 , ABI_id ) +Bytes X ) +Int 1 <- #lookup ( ACCT_ID_STORAGE , 5 ) *Int #lookup ( ACCT_ID_STORAGE , keccak ( #buf ( 32 , ABI_id ) +Bytes X ) +Int 1 ) /Int 1000000000000000000 ] , 6 ) /Int pow48 ) <Int pow48)
           => (true) 
        requires #lookup(ACCT_ID_STORAGE, 6) ==Int #WordPackUInt48UInt48(_, Tau)
        andBool #rangeUInt(48, TIME +Int Tau)

    claim [bytesDisjointSetCommutative1]: <k> runLemma( ACCT_ID_STORAGE [ keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 1 <- ABI_lot:Int ] [ keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 2 <- #WordPackAddrUInt48UInt48 ( CALLER_ID , TIME +Int ( maxUInt48 &Int #lookup ( ACCT_ID_STORAGE , 6 ) ) , #lookup ( ACCT_ID_STORAGE , keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 2 ) /Int pow208 ) ]
                          ==K
                        ACCT_ID_STORAGE [ keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 2 <- #WordPackAddrUInt48UInt48 ( CALLER_ID , TIME +Int ( maxUInt48 &Int #lookup ( ACCT_ID_STORAGE , 6 ) ) , #lookup ( ACCT_ID_STORAGE , keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 2 ) /Int pow208 ) ] [ keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 1 <- ABI_lot:Int ])
           => doneLemma(true) ... </k>
              

    claim (#lookup( M:Map [ keccak(_) <- _ ], I:Int ))
           => (#lookup( M , I )) 
      requires #rangeSmall(I)

    // Memory operations

    claim [bufferRangeSelectSymbolic]: <k> runLemma(#range(M:Bytes [ 0 := #buf(4, X) ] [ 0 <- 10 ] [ 1 <- 11 ] [ 2 <- 12 ] [ 3 <- 13 ], 0, 4)) =>
    doneLemma(10 : 11 : 12 : 13 : .Bytes) ... </k>

    claim ( M:Bytes [ 132 := #buf(32, B11) ] [ 128  := #buf(32, B21) +Bytes #buf(32, B22) ] ) => ( M [ 128 := (#buf(32, B21) +Bytes #buf(32, B22)) ] ) 
      requires #rangeUInt(256, B11) andBool #rangeUInt(256, B21) andBool #rangeUInt(256, B22)

    claim ( M:Bytes [ 128 := #buf(32, B31) +Bytes #buf(32, B32) ] [ 128 := #buf(32, B41) ] ) => ( M [ 128 := #buf(32, B41) ] [ 160 := #buf(32, B32) ] ) 
      requires #rangeUInt(256, B31) andBool #rangeUInt(256, B32) andBool #rangeUInt(256, B41)

    claim ( M:Bytes [ 128 := 217 : 99 : 141 : 54 : .Bytes ]
                                [ 132 := #buf(32, B11) ]
                                [ 128 := #buf(32, B21) +Bytes #buf(32, B22) +Bytes #buf(32, B23) +Bytes #buf(32, B24) +Bytes #buf(32, B25) ]
                                [ 128 := 217 : 99 : 141 : 54 : .Bytes ]
                                [ 132 := #buf(32, B11) ]
                                [ 128 := #buf(32, B31) +Bytes #buf(32, B32) ]
                                [ 128 := #buf(32, B41) ] )
           => ( M [ 128 := #buf(32, B41) ]
                           [ 160 := #buf(32, B32) ]
                           [ 192 := #buf(32, B23) +Bytes #buf(32, B24) +Bytes #buf(32, B25) ] )
          
          
     requires #rangeUInt(256, B11)
      andBool #rangeUInt(256, B21) andBool #rangeUInt(256, B22) andBool #rangeUInt(256, B23) andBool #rangeUInt(256, B24) andBool #rangeUInt(256, B25)
      andBool #rangeUInt(256, B31) andBool #rangeUInt(256, B32)
      andBool #rangeUInt(256, B41)

    claim (maxUInt48 &Int (maxUInt48 -Int 1) <Int maxUInt48 +Int 1) => (true) 
    claim (maxUInt160 &Int (maxUInt160 -Int 1) <Int maxUInt160 +Int 1) => (true) 

    claim ((maxUInt48 &Int maxUInt48) /Int maxUInt48) => (1) 
    claim ((maxUInt160 &Int maxUInt160) /Int maxUInt160) => (1) 

    claim ((maxUInt48 &Int M) /Int (maxUInt48 +Int 1)) => (0) 
      requires M >Int 0

    claim ((maxUInt160 &Int M) /Int (maxUInt160 +Int 1)) => (0) 
      requires M >Int 0

endmodule
