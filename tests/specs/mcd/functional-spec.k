requires "verification.k"

module FUNCTIONAL-SPEC-SYNTAX
    imports VERIFICATION

    syntax KItem ::= runLemma ( Step ) [symbol(runLemma)] | doneLemma ( Step )
 // -------------------------------------------------------
    rule <k> runLemma(S) => doneLemma(S) ... </k>

    syntax Step ::= Bool | Int | Bytes
 // ----------------------------------

endmodule

module FUNCTIONAL-SPEC
    imports FUNCTIONAL-SPEC-SYNTAX

    // Arithmetic

    claim <k> runLemma((X +Int pow256) -Int chop(Y)) => doneLemma(X -Int Y) ... </k>
      requires #rangeUInt(256, X)
       andBool #rangeSInt(256, Y)
       andBool Y <Int 0

    claim <k> runLemma(chop(Art_i *Int (ABI_rate +Int pow256))) => doneLemma(chop(Art_i *Int ABI_rate)) ... </k>
      requires #rangeUInt(256, Art_i)
       andBool Art_i <=Int maxSInt256
       andBool #rangeSInt(256, Art_i *Int ABI_rate)

    claim <k> runLemma(maxUInt48 &Int ABI_x <=Int maxUInt48 &Int ABI_x +Int ABI_y) => doneLemma(false) ... </k>
      requires #rangeUInt(48, ABI_x)
       andBool #rangeUInt(48, ABI_y)
       andBool notBool #rangeUInt(48, ABI_x +Int ABI_y)

    claim <k> runLemma( (maxUInt48 &Int W1) +Int (maxUInt160 &Int W2) ) => doneLemma( A +Int C ) ... </k>
          requires (W1 ==Int #WordPackUInt48UInt48(A, B))
           andBool (W2 ==Int #WordPackAddrUInt48UInt48(C, D, E))
           andBool #rangeUInt(48, A) andBool #rangeUInt(48, B)
           andBool #rangeAddress(C) andBool #rangeUInt(48, D) andBool #rangeUInt(48, E)

    claim <k> runLemma(bool2Word(ABI_src:Int ==Int CALLER_ID:Int) |Int bool2Word(X)) => doneLemma(bool2Word(ABI_src ==Int CALLER_ID orBool X)) ... </k>
      requires #rangeUInt(256, ABI_src)
       andBool #rangeUInt(256, CALLER_ID)

    claim <k> runLemma(bool2Word(ABI_src ==Int CALLER_ID orBool X) ==Int 0) => doneLemma(notBool(ABI_src ==Int CALLER_ID orBool X)) ... </k>
      requires #rangeUInt(256, ABI_src)
       andBool #rangeUInt(256, CALLER_ID)

    claim <k> runLemma( chop( A -Int B ) <=Int A  ) =>  doneLemma( false ) ... </k>
      requires #rangeUInt(256, A) andBool #rangeUInt(256, B) andBool A -Int B <Int 0

    // WordPack

    claim <k> runLemma((GAL |Int (notMaxUInt160 &Int GUY_TIC_END)) modInt pow256) => doneLemma(GAL |Int (notMaxUInt160 &Int GUY_TIC_END)) ... </k>
      requires #rangeUInt(256, GUY_TIC_END)
       andBool #rangeAddress(GAL)

    claim <k> runLemma(TIME +Int (TTL_TAU /Int pow48)) => doneLemma(TIME +Int TAU) ... </k>
      requires TTL_TAU ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool #rangeUInt(48, TTL) andBool #rangeUInt(48, TAU)

    claim <k> runLemma(maxUInt48 &Int ((GAL |Int (notMaxUInt160 &Int GUY_TIC_END)) /Int pow160)) => doneLemma(TIC) ... </k>
      requires GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL) andBool #rangeAddress(GUY) andBool #rangeUInt(48, TIC) andBool #rangeUInt(48, END)

    claim <k> runLemma(maxUInt160 &Int (GAL |Int (notMaxUInt160 &Int GUY_TIC_END))) => doneLemma(GAL) ... </k>
      requires GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL) andBool #rangeAddress(GUY) andBool #rangeUInt(48, TIC) andBool #rangeUInt(48, END)

    claim [wordPackSimplify1]: <k> runLemma((((TIME +Int (maxUInt48 &Int (TTL_TAU /Int pow48))) *Int pow208) |Int (maxUInt208 &Int (GAL |Int (notMaxUInt160 &Int GUY_TIC_END))))) => doneLemma(#WordPackAddrUInt48UInt48(GAL, TIC, TIME +Int TAU)) ... </k>
      requires TTL_TAU     ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeAddress(GAL) andBool #rangeUInt(48, TTL) andBool #rangeUInt(48, TAU) andBool #rangeUInt(48, TIME +Int TAU)
       andBool #rangeAddress(GUY) andBool #rangeUInt(48, TIC) andBool #rangeUInt(48, END)

    claim [wordPackSimplify2]: <k> runLemma((((TIME +Int (maxUInt48 &Int TTL_TAU)) *Int pow160) |Int (115792089237315784047431654708638870748305248246218003188207458632603225030655 &Int GUY_TIC_END))) => doneLemma(#WordPackAddrUInt48UInt48(GUY, TIME +Int TTL, END)) ... </k>
      requires TTL_TAU     ==Int #WordPackUInt48UInt48(TTL, TAU)
       andBool GUY_TIC_END ==Int #WordPackAddrUInt48UInt48(GUY, TIC, END)
       andBool #rangeUInt(48, TTL) andBool #rangeUInt(48, TAU) andBool #rangeUInt(48, TIME +Int TTL)
       andBool #rangeAddress(GUY) andBool #rangeUInt(48, TIC) andBool #rangeUInt(48, END)

    claim <k> runLemma(TIME +Int ( maxUInt48 &Int #lookup ( ((6 |-> #WordPackUInt48UInt48(Junk, Tau)) ACCT_ID_STORAGE) [ keccak ( #buf ( 32 , ABI_id ) +Bytes X ) +Int 1 <- #lookup ( ACCT_ID_STORAGE , 5 ) *Int #lookup ( ACCT_ID_STORAGE , keccak ( #buf ( 32 , ABI_id ) +Bytes X ) +Int 1 ) /Int 1000000000000000000 ] , 6 ) /Int pow48 ) <Int pow48)
           => doneLemma(true) ... </k>
        requires #rangeUInt(48, Junk) andBool #rangeUInt(48, Tau) andBool #rangeUInt(48, TIME +Int Tau)

    claim [bytesDisjointSetCommutative1]: <k> runLemma( ACCT_ID_STORAGE [ keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 1 <- ABI_lot:Int ] [ keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 2 <- #WordPackAddrUInt48UInt48 ( CALLER_ID , TIME +Int ( maxUInt48 &Int #lookup ( ACCT_ID_STORAGE , 6 ) ) , #lookup ( ACCT_ID_STORAGE , keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 2 ) /Int pow208 ) ]
                          ==K
                        ACCT_ID_STORAGE [ keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 2 <- #WordPackAddrUInt48UInt48 ( CALLER_ID , TIME +Int ( maxUInt48 &Int #lookup ( ACCT_ID_STORAGE , 6 ) ) , #lookup ( ACCT_ID_STORAGE , keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 2 ) /Int pow208 ) ] [ keccak ( #buf ( 32 , ABI_id ) +Bytes X) +Int 1 <- ABI_lot:Int ])
           => doneLemma(true) ... </k>

    // Memory operations

    claim <k> runLemma( M:Bytes [ 132 := #buf(32, B11) ] [ 128  := #buf(32, B21) +Bytes #buf(32, B22) ] ) => doneLemma( M [ 128 := (#buf(32, B21) +Bytes #buf(32, B22)) ] ) ... </k>
      requires #rangeUInt(256, B11) andBool #rangeUInt(256, B21) andBool #rangeUInt(256, B22)

    claim <k> runLemma( M:Bytes [ 128 := 217 : 99 : 141 : 54 : .Bytes ]
                                [ 132 := #buf(32, B11) ]
                                [ 128 := #buf(32, B21) +Bytes #buf(32, B22) +Bytes #buf(32, B23) +Bytes #buf(32, B24) +Bytes #buf(32, B25) ]
                                [ 128 := 217 : 99 : 141 : 54 : .Bytes ]
                                [ 132 := #buf(32, B11) ]
                                [ 128 := #buf(32, B31) +Bytes #buf(32, B32) ]
                                [ 128 := #buf(32, B41) ] )
           => doneLemma( M [ 128 := #buf(32, B41) ]
                           [ 160 := #buf(32, B32) ]
                           [ 192 := #buf(32, B23) +Bytes #buf(32, B24) +Bytes #buf(32, B25) ] )
          ...
          </k>
     requires #rangeUInt(256, B11)
      andBool #rangeUInt(256, B21) andBool #rangeUInt(256, B22) andBool #rangeUInt(256, B23) andBool #rangeUInt(256, B24) andBool #rangeUInt(256, B25)
      andBool #rangeUInt(256, B31) andBool #rangeUInt(256, B32)
      andBool #rangeUInt(256, B41)

    // keccak

    claim [keccak-neq]:
      <k> runLemma (
          keccak ( #buf ( 32 , ABI_u:Int ) +Bytes #buf ( 32 , keccak ( #buf ( 32 , ABI_i:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03" ) ) ) +Int 1
            ==Int
          keccak ( #buf ( 32 , ABI_i:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02" ) +Int 1
        ) => doneLemma(
          false
        ) ... </k>

    claim [lookup-keccak-neq]:
      <k> runLemma (
        #lookup (
            ( ( keccak ( #buf ( 32 , ABI_u:Int ) +Bytes #buf ( 32 , keccak ( #buf ( 32 , ABI_i:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x03" ) ) ) +Int 1 ) |-> Urn_art:Int )
            ACCT_ID_STORAGE:Map,
            ( keccak ( #buf ( 32 , ABI_i:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02" ) +Int 1 ) )
      ) => doneLemma(
        #lookup (
          ACCT_ID_STORAGE:Map,
          ( keccak ( #buf ( 32 , ABI_i:Int ) +Bytes b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x02" ) +Int 1 ) )
      ) ... </k>

endmodule
