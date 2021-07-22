requires "krypto.md"
requires "json.md"

module EVM
    imports STRING
    imports EVM-DATA

    configuration
      <kevm>
        <k> $PGM:EthereumSimulation </k>
        <ethereum>
          <evm>
            <callState> // KEEP 
              <program> .ByteArray </program> // KEEP
              <jumpDests> .Set </jumpDests> // KEEP
              <pc>          0          </pc>                  // \mu_pc
            </callState>
          </evm>
          <network>
            <accounts> // KEEP
              <account multiplicity="*" type="Map">
                <storage>     .Map                   </storage> // KEEP
              </account>
            </accounts>
          </network>
        </ethereum>
      </kevm>

  syntax EthereumSimulation

    syntax Set ::= #computeValidJumpDests( ByteArray )            [function, memo]
                 | #computeValidJumpDests( ByteArray , Int , List ) [function, klabel(#computeValidJumpDestsAux)]
  // ---------------------------------------------------------------------------------------------------------
    rule #computeValidJumpDests(PGM) => #computeValidJumpDests(PGM, 0, .List)

    syntax Set ::= #computeValidJumpDestsWithinBound(ByteArray, Int, List) [function]
  // ---------------------------------------------------------------------------------
    rule #computeValidJumpDests(PGM, I, RESULT) => List2Set(RESULT) requires I >=Int #sizeByteArray(PGM)
    rule #computeValidJumpDests(PGM, I, RESULT) => #computeValidJumpDestsWithinBound(PGM, I, RESULT) requires I <Int #sizeByteArray(PGM)

    rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int 1, RESULT ListItem(I)) requires PGM [ I ] ==Int 91
    rule #computeValidJumpDestsWithinBound(PGM, I, RESULT) => #computeValidJumpDests(PGM, I +Int #widthOpCode(PGM [ I ]), RESULT) requires notBool PGM [ I ] ==Int 91


// [#] #widthOpCode
    syntax Int ::= #widthOpCode(Int) [function]
 // -------------------------------------------
    rule #widthOpCode(W) => W -Int 94 requires W >=Int 96 andBool W <=Int 127
    rule #widthOpCode(_) => 1 [owise]

endmodule


module EVM-DATA
    imports EVM-TYPES
    imports SERIALIZATION
    imports STRING-BUFFER
    imports MAP-SYMBOLIC
    imports COLLECTIONS
endmodule

module ETHEREUM-SIMULATION
    imports EVM
endmodule

module EVM-TYPES
    imports INT
    imports STRING
    imports COLLECTIONS
    imports BYTES

    syntax Int ::= "pow256"
 // ----------------------------------------
    rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936 [macro]

    syntax Int ::= "minUInt256"
 // --------------------------------
    rule minUInt256 => 0 [macro]

    syntax Bool ::= #rangeUInt    ( Int , Int )
  // -------------------------------------------
    rule #rangeUInt(256, X) => #range(minUInt256 <= X < pow256) [macro]

    syntax Bool ::= "#range" "(" Int "<=" Int "<"  Int ")"
 // ------------------------------------------------------
    rule #range ( LB <= X <  UB ) => LB <=Int X andBool X  <Int UB [macro]

    syntax Int ::= chop ( Int ) [function, functional, smtlib(chop)]
 // ----------------------------------------------------------------
    rule chop ( I:Int ) => I modInt pow256 [concrete, smt-lemma]

    syntax Int ::= Int "<<Byte" Int [function]

    syntax WordStack [flatPredicate]
    syntax WordStack ::= ".WordStack"      [smtlib(_dotWS)]
                       | Int ":" WordStack [klabel(_:_WS), smtlib(_WS_)]
 // --------------------------------------------------------------------

    syntax Bytes ::= Int ":" Bytes [function]
 // -----------------------------------------
    rule I : BS => Int2Bytes(1, I, BE) ++ BS requires I <Int 256 // KEEP

    syntax ByteArray = Bytes
    syntax ByteArray ::= ".ByteArray"
 // ---------------------------------
    rule .ByteArray => .Bytes [macro]

    syntax ByteArray ::= #asByteStack ( Int ) [function, functional]
 // ----------------------------------------------------------------
    rule #asByteStack(W) => Int2Bytes(W, BE, Unsigned) [concrete] // KEEP

    syntax ByteArray ::= ByteArray "++" ByteArray [function, functional, right, klabel(_++_WS), smtlib(_plusWS_)]
 // -------------------------------------------------------------------------------------------------------------
    rule WS ++ WS' => WS +Bytes WS' [concrete]

    syntax Int ::= #sizeByteArray ( ByteArray ) [function, functional, klabel(sizeByteArray), smtlib(sizeByteArray)]
 // ----------------------------------------------------------------------------------------------------------------
    rule #sizeByteArray ( WS ) => lengthBytes(WS) [concrete]

    syntax ByteArray ::= #padToWidth      ( Int , ByteArray ) [function, functional]
                       | #padRightToWidth ( Int , ByteArray ) [function, functional]
 // --------------------------------------------------------------------------------
    rule                        #padToWidth(N, BS)      =>               BS        requires notBool (N >=Int 0)
    rule [padToWidthNonEmpty] : #padToWidth(N, BS)      =>  padLeftBytes(BS, N, 0) requires          N >=Int 0
    rule                        #padRightToWidth(N, BS) =>               BS        requires notBool (N >=Int 0)
    rule                        #padRightToWidth(N, BS) => padRightBytes(BS, N, 0) requires          N >=Int 0

    syntax Account ::= ".Account" | Int
 // -----------------------------------


endmodule

module SERIALIZATION
    imports KRYPTO
    imports EVM-TYPES
    imports STRING-BUFFER

    syntax Int ::= keccak ( ByteArray ) [function, functional, smtlib(smt_keccak)]
 // ------------------------------------------------------------------------------
    rule [keccak]: keccak(WS) => #parseHexWord(Keccak256(#unparseByteStack(WS)))

    syntax Int ::= #parseHexWord ( String ) [function]
                 | #parseWord    ( String ) [function]
 // --------------------------------------------------
    rule #parseHexWord("")   => 0
    rule #parseHexWord("0x") => 0
    rule #parseHexWord(S)    => String2Base(replaceAll(S, "0x", ""), 16) requires (S =/=String "") andBool (S =/=String "0x")

    rule #parseWord("") => 0
    rule #parseWord(S)  => #parseHexWord(S) requires lengthString(S) >=Int 2 andBool substrString(S, 0, 2) ==String "0x"
    rule #parseWord(S)  => String2Int(S) [owise]

    syntax String ::= #alignHexString ( String ) [function, functional]
 // -------------------------------------------------------------------
    rule #alignHexString(S) => S             requires         lengthString(S) modInt 2 ==Int 0
    rule #alignHexString(S) => "0" +String S requires notBool lengthString(S) modInt 2 ==Int 0

    syntax ByteArray ::= #parseHexBytes     ( String ) [function]
                       | #parseHexBytesAux  ( String ) [function]
                       | #parseByteStack    ( String ) [function, memo]
                       | #parseByteStackRaw ( String ) [function]
 // -------------------------------------------------------------------
    rule #parseByteStack(S) => #parseHexBytes(replaceAll(S, "0x", ""))

    rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))
    rule #parseHexBytesAux("") => .ByteArray
    rule #parseHexBytesAux(S)  => Int2Bytes(lengthString(S) /Int 2, String2Base(S, 16), BE)
      requires lengthString(S) >=Int 2

    rule #parseByteStackRaw(S) => String2Bytes(S)


    syntax String ::= #unparseByteStack ( ByteArray ) [function, klabel(unparseByteStack), symbol]
 // ----------------------------------------------------------------------------------------------
    rule #unparseByteStack(WS) => Bytes2String(WS)

    syntax String ::= #padByte( String ) [function]
 // -----------------------------------------------
    rule #padByte( S ) => S             requires lengthString(S) ==K 2
    rule #padByte( S ) => "0" +String S requires lengthString(S) ==K 1

    syntax String ::= #unparseQuantity( Int ) [function]
 // ----------------------------------------------------
    rule #unparseQuantity( I ) => "0x" +String Base2String(I, 16)

endmodule

module BUF-SYNTAX
    imports EVM

    syntax ByteArray ::= #bufStrict ( Int , Int ) [function]
    syntax ByteArray ::= #buf ( Int , Int ) [function, functional, smtlib(buf)]

endmodule

module BUF
    imports BUF-SYNTAX
    imports BUF-KORE

    // KEEP
    rule #bufStrict(SIZE, DATA) => #buf(SIZE, DATA)
      requires #range(0 <= DATA < (2 ^Int (SIZE *Int 8)))

    // KEEP
    rule #buf(SIZE, DATA) => #padToWidth(SIZE, #asByteStack(DATA %Int (2 ^Int (SIZE *Int 8))))
      [concrete]

endmodule

module BUF-KORE [kore, symbolic]
    imports BUF-SYNTAX

    rule #bufStrict(_, _) => #Bottom              [owise]

endmodule

module HASHED-LOCATIONS
    imports EVM
    imports BUF

    syntax Int ::= #hashedLocation( String , Int , IntList ) [function, klabel(hashLoc), smtlib(hashLoc)]
 // -----------------------------------------------------------------------------------------------------
    rule #hashedLocation(_LANG, BASE, .IntList      ) => BASE
    rule #hashedLocation( LANG, BASE, OFFSET OFFSETS) => #hashedLocation(LANG, #hashedLocation(LANG, BASE, OFFSET .IntList), OFFSETS) requires OFFSETS =/=K .IntList

    rule #hashedLocation("Solidity", BASE, OFFSET .IntList) => keccak(#bufStrict(32, OFFSET) ++ #bufStrict(32, BASE)) requires #rangeUInt(256, BASE) andBool #rangeUInt(256, OFFSET)

    syntax IntList ::= List{Int, ""} [klabel(intList), smtlib(intList)]
 // -------------------------------------------------------------------
endmodule