requires "evm.k"
requires "edsl.k"

module LEMMAS
    imports EVM
    imports EDSL

    rule #asWord( BUF => #drop(1, BUF) ) requires BUF [ 0 ] ==Int 0  [simplification]

    rule WS ++ .ByteArray => WS  [simplification]

    rule #sizeByteArray(W : WS)        => 1 +Int #sizeByteArray(WS)                       [simplification]
    rule #sizeByteArray(#buf(N, _)  )  => N                                               [simplification]
    rule #sizeByteArray(BUF1 ++ BUF2)  => #sizeByteArray(BUF1) +Int #sizeByteArray(BUF2)  [simplification]
    rule #sizeByteArray(#drop(N, BUF)) => maxInt(#sizeByteArray(BUF) -Int N, 0)           [simplification]
    rule #sizeByteArray(M [ N := BUF ]) => maxInt(#sizeByteArray(M), #sizeByteArray(BUF) +Int N)           [simplification]

    rule #take(N, BUF)          => BUF                                              requires N ==Int #sizeByteArray(BUF)   [simplification]
    rule #take(N, BUF1 ++ BUF2) => #take(N, BUF1)                                   requires N <=Int #sizeByteArray(BUF1)  [simplification]
    rule #take(N, BUF1 ++ BUF2) => BUF1 ++ #take(N -Int #sizeByteArray(BUF1), BUF2) requires N  >Int #sizeByteArray(BUF1)  [simplification]

    rule #drop(N, BUF)          => .ByteArray                               requires N >=Int #sizeByteArray(BUF)   [simplification]
    rule #drop(N, BUF1 ++ BUF2) => #drop(N -Int #sizeByteArray(BUF1), BUF2) requires N >=Int #sizeByteArray(BUF1)  [simplification]
    rule #drop(N, BUF1 ++ BUF2) => #drop(N, BUF1) ++ BUF2                   requires N  <Int #sizeByteArray(BUF1)  [simplification]

    rule #asWord(#buf(N, BUF)) => BUF  [simplification]

    rule #asWord(BUF) /Int 26959946667150639794667015087019630673637144422540572481103610249216 => #asWord(#take(4, BUF))  [simplification]

    rule M [ N := BUF ] [ N := BUF' ] => M [ N := BUF' ] requires #sizeByteArray(BUF) ==Int #sizeByteArray(BUF')  [simplification]
    rule M [ N := .ByteArray ] => M requires #sizeByteArray(M) >=Int N  [simplification]

    rule BUF [ L .. W ] => .ByteArray requires W <=Int 0                    [simplification]
    rule BUF [ 0 .. W ] => BUF        requires W ==Int #sizeByteArray(BUF)  [simplification]
    rule BUF [ L .. W ] => .ByteArray requires L  >Int #sizeByteArray(BUF)  [simplification]

    rule #range(M, N, K) => .ByteArray requires notBool K >Int 0  [simplification]

    rule #range(M [ N := BUF:ByteArray ], L, K) => #range(M, L, minInt(K, N -Int L)) ++ #range(M [ N := BUF ], N, K -Int minInt(K, N -Int L))
      requires K >Int 0
       andBool L <Int N
      [simplification]

    rule #range(M [ N := BUF ], L, K) => BUF [ L -Int N .. minInt(K, #sizeByteArray(BUF) -Int (L -Int N)) ] ++ #range(M, N +Int #sizeByteArray(BUF), K -Int minInt(K, #sizeByteArray(BUF) -Int (L -Int N)))
      requires K  >Int 0
       andBool L >=Int N
       andBool L  <Int N +Int #sizeByteArray(BUF)
      [simplification]

    rule #range(M [ N := BUF ], L, K) => #range(M, L, K)
      requires K  >Int 0
       andBool L >=Int N +Int #sizeByteArray(BUF)
      [simplification]

    rule keccak(BUF1 ++ BUF2) => hash2(#asWord(BUF1), #asWord(BUF2)) requires #sizeByteArray(BUF1) ==Int 32 andBool #sizeByteArray(BUF2) ==Int 32  [simplification]

    syntax Bool ::= #isRegularWordStack ( WordStack ) [function]
 // -------------------------------------------------------
    rule #isRegularWordStack(N : WS => WS)
    rule #isRegularWordStack(.WordStack) => true

    // for Vyper
    rule #padToWidth(N, #asByteStack(#asWord(WS))) => WS
      requires #noOverflow(WS) andBool N ==Int #sizeByteArray(WS)
      [simplification]

    // for Solidity
    rule #asWord(WS) /Int D => #asWord(#take(#sizeByteArray(WS) -Int log256Int(D), WS))
      requires D ==Int 256 ^Int log256Int(D) andBool D >=Int 0
       andBool #sizeByteArray(WS) >=Int log256Int(D)
       andBool #noOverflow(WS)
      [simplification]

    syntax Bool ::= #noOverflow    ( ByteArray ) [function]
                  | #noOverflowAux ( ByteArray ) [function]
 // -------------------------------------------------------
    rule #noOverflow(WS) => #sizeByteArray(WS) <=Int 32 andBool #noOverflowAux(WS)

    rule #noOverflowAux(BA        ) => 0 <=Int BA[0] andBool BA[0] <Int 256 andBool #noOverflowAux(#drop(1,BA)) requires #sizeByteArray(BA) >Int 0
    rule #noOverflowAux(.ByteArray) => true

    // TODO: drop hash1 and keccakIntList once new vyper hashed location scheme is captured in edsl.md

    syntax Int ::= hash1(Int)      [function, smtlib(smt_hash1)]
                 | hash2(Int, Int) [function, smtlib(smt_hash2)]

    rule hash1(V) => keccak(#padToWidth(32, #asByteStack(V)))
      requires 0 <=Int V andBool V <Int pow256
      [concrete]

    rule hash2(V1, V2) => keccak(   #padToWidth(32, #asByteStack(V1))
                                 ++ #padToWidth(32, #asByteStack(V2)))
      requires 0 <=Int V1 andBool V1 <Int pow256
       andBool 0 <=Int V2 andBool V2 <Int pow256
      [concrete]

    rule keccakIntList(V:Int .IntList) => hash1(V)               [simplification]
    rule keccakIntList(V1:Int V2:Int .IntList) => hash2(V1, V2)  [simplification]

    // for terms came from bytecode not via #hashedLocation
    rule keccak(WS) => keccakIntList(byteStack2IntList(WS))
      requires ( #sizeByteArray(WS) ==Int 32 orBool #sizeByteArray(WS) ==Int 64 )
      [simplification]

    rule N +Int 0 => N  [simplification]

    rule N -Int 0 => N  [simplification]

    rule 1 *Int N => N  [simplification]
    rule N *Int 1 => N  [simplification]
    rule 0 *Int _ => 0  [simplification]
    rule _ *Int 0 => 0  [simplification]

    rule N /Int 1 => N  [simplification]

    rule 0 |Int N => N  [simplification]
    rule N |Int 0 => N  [simplification]
    rule N |Int N => N  [simplification]

    rule 0 &Int N => 0  [simplification]
    rule N &Int 0 => 0  [simplification]
    rule N &Int N => N  [simplification]

    // 0xffff...f &Int N = N
    rule MASK &Int N => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK
      [simplification]

    // N &Int 0xffff...f = N
    rule N &Int MASK => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK
      [simplification]

    // for gas calculation
    rule A -Int (#if C #then B1 #else B2 #fi) => #if C #then (A -Int B1) #else (A -Int B2) #fi  [simplification]

    rule (#if C #then B1 #else B2 #fi) +Int A => #if C #then (B1 +Int A) #else (B2 +Int A) #fi  [simplification]

    rule X >Int Y => Y <Int X    [simplification]
    rule X >=Int Y => Y <=Int X  [simplification]

    rule notBool (X <Int Y) => Y <=Int X  [simplification]
    rule notBool (X <=Int Y) => Y <Int X  [simplification]

    rule bool2Word(A) |Int bool2Word(B) => bool2Word(A  orBool B)  [simplification]
    rule bool2Word(A) &Int bool2Word(B) => bool2Word(A andBool B)  [simplification]

    rule 1 |Int bool2Word(B) => 1             [simplification]
    rule 1 &Int bool2Word(B) => bool2Word(B)  [simplification]

    rule bool2Word(B) |Int 1 => 1             [simplification]
    rule bool2Word(B) &Int 1 => bool2Word(B)  [simplification]

    rule bool2Word(A)  ==K 0 => notBool(A)  [simplification]
    rule bool2Word(A)  ==K 1 => A           [simplification]
    rule bool2Word(A) =/=K 0 => A           [simplification]
    rule bool2Word(A) =/=K 1 => notBool(A)  [simplification]

    rule chop(bool2Word(B)) => bool2Word(B)  [simplification]

    rule 0 <=Int X &Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256  [simplification]
    rule         X &Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256  [simplification]

    rule 0 <=Int #asWord(WS)          => true  [simplification]
    rule #asWord(WS) <Int pow256      => true  [simplification]

    rule 0 <=Int hash1(_)             => true  [simplification]
    rule         hash1(_) <Int pow256 => true  [simplification]

    rule 0 <=Int hash2(_,_)             => true  [simplification]
    rule         hash2(_,_) <Int pow256 => true  [simplification]

    rule 0 <=Int chop(V)             => true  [simplification]
    rule         chop(V) <Int pow256 => true  [simplification]

    rule 0 <=Int keccak(V)             => true  [simplification]
    rule         keccak(V) <Int pow256 => true  [simplification]

    rule 0 <=Int keccakIntList(_)             => true  [simplification]
    rule         keccakIntList(_) <Int pow256 => true  [simplification]

    rule X <=Int maxUInt256 => X <Int pow256  [simplification]
    rule X <=Int maxUInt160 => X <Int pow160  [simplification]
    rule X <=Int 255        => X <Int 256     [simplification]

    rule chop(I) => I requires 0 <=Int I andBool I <Int pow256  [simplification]

    rule N <=Int maxInt(P, Q) => true requires N <=Int P orBool N <=Int Q  [simplification]

    rule 0 <=Int #sizeWordStack ( _ , _ ) => true [smt-lemma]

    rule 0 <=Int lengthBytes ( _ ) => true [smt-lemma]

endmodule
