



requires "evm.k"
requires "edsl.k"

module LEMMAS
    imports EVM
    imports EDSL
    imports K-REFLECTION













    syntax Int ::= nthbyteof ( Int , Int , Int ) [function, smtlib(smt_nthbyteof), proj]
 // ------------------------------------------------------------------------------------
    rule nthbyteof(V, I, N) => nthbyteof(V /Int 256, I, N -Int 1) when N  >Int (I +Int 1) [concrete]
    rule nthbyteof(V, I, N) =>           V modInt 256             when N ==Int (I +Int 1) [concrete]









    rule #asWord( nthbyteof(V,  0, 32)
                : nthbyteof(V,  1, 32)
                : nthbyteof(V,  2, 32)
                : nthbyteof(V,  3, 32)
                : nthbyteof(V,  4, 32)
                : nthbyteof(V,  5, 32)
                : nthbyteof(V,  6, 32)
                : nthbyteof(V,  7, 32)
                : nthbyteof(V,  8, 32)
                : nthbyteof(V,  9, 32)
                : nthbyteof(V, 10, 32)
                : nthbyteof(V, 11, 32)
                : nthbyteof(V, 12, 32)
                : nthbyteof(V, 13, 32)
                : nthbyteof(V, 14, 32)
                : nthbyteof(V, 15, 32)
                : nthbyteof(V, 16, 32)
                : nthbyteof(V, 17, 32)
                : nthbyteof(V, 18, 32)
                : nthbyteof(V, 19, 32)
                : nthbyteof(V, 20, 32)
                : nthbyteof(V, 21, 32)
                : nthbyteof(V, 22, 32)
                : nthbyteof(V, 23, 32)
                : nthbyteof(V, 24, 32)
                : nthbyteof(V, 25, 32)
                : nthbyteof(V, 26, 32)
                : nthbyteof(V, 27, 32)
                : nthbyteof(V, 28, 32)
                : nthbyteof(V, 29, 32)
                : nthbyteof(V, 30, 32)
                : nthbyteof(V, 31, 32)
                : .WordStack ) => V
      requires 0 <=Int V andBool V <Int pow256

    rule #asWord( 0 : W1 : WS  =>  W1 : WS )

    rule nthbyteof(N, 0, 1) => N

    rule WS ++ .WordStack => WS

    rule #sizeWordStack(#buf(N, _)  , M) => M +Int N
    rule #sizeWordStack(BUF1 ++ BUF2, M) => M +Int #sizeWordStack(BUF1) +Int #sizeWordStack(BUF2)
    rule #sizeWordStack(#drop(N, BUF))   => maxInt(#sizeWordStack(BUF) -Int N, 0)

    rule #take(N, #buf(N, BUF)) => #buf(N, BUF)
    rule #take(N, BUF1 ++ BUF2) => #take(N, BUF1) requires N <=Int #sizeWordStack(BUF1)

    rule #drop(N, BUF)           => .WordStack requires #sizeWordStack(BUF) <=Int N
    rule #drop(N, #drop(M, BUF)) => #drop(N +Int M, BUF)
    rule #drop(N, BUF1 ++ BUF2)  => #drop(N -Int #sizeWordStack(BUF1), BUF2) requires N >=Int #sizeWordStack(BUF1)
    rule #drop(N, BUF1 ++ BUF2)  => #drop(N, BUF1) ++ BUF2 requires N <Int #sizeWordStack(BUF1)

    rule #asWord(#buf(N, BUF)) => BUF

    rule #asWord(W0 : W1 : W2 : W3 : #take(28, BUF)) /Int 26959946667150639794667015087019630673637144422540572481103610249216 => #asWord(W0 : W1 : W2 : W3 : .WordStack)

    rule M [ N := #buf(K, BUF) ] [ L <- V ] => M [ L <- V ] [ N := #buf(K, BUF) ] requires L >=Int N +Int K
    rule M [ N := #buf(K, BUF) ] [ N := #buf(K, BUF') ] => M [ N := #buf(K, BUF') ]

    rule M [ N := BUF ] => M requires #sizeWordStack(BUF) <=Int 0
    rule M [ N := BUF ] [ N <- V ] => M [ N <- V ] [ N +Int 1 := #drop(1, BUF) ]

    rule #buf(W, BUF) [ L .. K ] => .ByteArray requires L  >Int W
    rule #buf(W, BUF) [ L .. K ] => .ByteArray requires K <=Int 0
    rule #buf(W, BUF) [ 0 .. W ] => #buf(W, BUF)

    rule #range(M, N, K) => .ByteArray requires notBool K >Int 0

    rule #range(M [ N := #padToWidth(W, BUF) ], L, K) => #range(M, L, K)
      requires L +Int K <=Int N
        orBool N +Int W  <Int L

    rule #range(M [ N := #padToWidth(W, BUF) ], N, W) => BUF

    rule #range(M [ N := #buf(W, BUF) ], L, K) => #range(M, L, minInt(K, N -Int L)) ++ #range(M [ N := #buf(W, BUF) ], N, K -Int minInt(K, N -Int L))
      requires K >Int 0
       andBool L <Int N

    rule #range(M [ N := #buf(W, BUF) ], L, K) => #buf(W, BUF) [ L -Int N .. minInt(K, W -Int (L -Int N)) ] ++ #range(M, N +Int W, K -Int minInt(K, W -Int (L -Int N)))
      requires K  >Int 0
       andBool L >=Int N
       andBool L  <Int N +Int W

    rule #range(M [ N := #buf(W, BUF) ], L, K) => #range(M, L, K)
      requires K  >Int 0
       andBool L >=Int N +Int W

    rule keccak(BUF1 ++ BUF2) => hash2(#asWord(BUF1), #asWord(BUF2)) requires #sizeWordStack(BUF1) ==Int 32 andBool #sizeWordStack(BUF2) ==Int 32

    syntax Bool ::= #isRegularWordStack ( WordStack ) [function]
 // -------------------------------------------------------
    rule #isRegularWordStack(N : WS => WS)
    rule #isRegularWordStack(.WordStack) => true

    // for Vyper
    rule #padToWidth(N, #asByteStack(#asWord(WS))) => WS
      requires #noOverflow(WS) andBool N ==Int #sizeWordStack(WS)

    // for Solidity
    rule #asWord(WS) /Int D => #asWord(#take(#sizeWordStack(WS) -Int log256Int(D), WS))
      requires D ==Int 256 ^Int log256Int(D) andBool D >=Int 0
       andBool #sizeWordStack(WS) >=Int log256Int(D)
       andBool #noOverflow(WS)

    syntax Bool ::= #noOverflow    ( WordStack ) [function]
                  | #noOverflowAux ( WordStack ) [function]
 // -------------------------------------------------------
    rule #noOverflow(WS) => #sizeWordStack(WS) <=Int 32 andBool #noOverflowAux(WS)

    rule #noOverflowAux(W : WS)     => 0 <=Int W andBool W <Int 256 andBool #noOverflowAux(WS)
    rule #noOverflowAux(.WordStack) => true

    syntax WordStack ::= #asByteStackInWidth    ( Int, Int )                 [function]
                       | #asByteStackInWidthAux ( Int, Int, Int, WordStack ) [function]
 // -----------------------------------------------------------------------------------
    rule #asByteStackInWidth(X, N) => #asByteStackInWidthAux(X, N -Int 1, N, .WordStack)
      requires #rangeBytes(N, X)

    rule #asByteStackInWidthAux(X, I => I -Int 1, N, WS => nthbyteof(X, I, N) : WS) when I >=Int 0
    rule #asByteStackInWidthAux(X,            -1, N, WS) => WS





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

    rule keccakIntList(V:Int .IntList) => hash1(V)
    rule keccakIntList(V1:Int V2:Int .IntList) => hash2(V1, V2)

    // for terms came from bytecode not via #hashedLocation
    rule keccak(WS) => keccakIntList(byteStack2IntList(WS))
      requires ( notBool #isConcrete(WS) )
       andBool ( #sizeWordStack(WS) ==Int 32 orBool #sizeWordStack(WS) ==Int 64 )










    rule N +Int 0 => N

    rule N -Int 0 => N

    rule 1 *Int N => N
    rule N *Int 1 => N
    rule 0 *Int _ => 0
    rule _ *Int 0 => 0

    rule N /Int 1 => N

    rule 0 |Int N => N
    rule N |Int 0 => N
    rule N |Int N => N

    rule 0 &Int N => 0
    rule N &Int 0 => 0
    rule N &Int N => N







    //orienting symbolic term to be first, converting -Int to +Int for concrete values.
    rule I +Int B => B          +Int I when #isConcrete(I) andBool notBool #isConcrete(B)
    rule A -Int I => A +Int (0 -Int I) when notBool #isConcrete(A) andBool #isConcrete(I)

    rule (A +Int I2) +Int I3 => A +Int (I2 +Int I3) when notBool #isConcrete(A) andBool #isConcrete(I2) andBool #isConcrete(I3)

    rule I1 +Int (B +Int I3) => B +Int (I1 +Int I3) when #isConcrete(I1) andBool notBool #isConcrete(B) andBool #isConcrete(I3)
    rule I1 -Int (B +Int I3) => (I1 -Int I3) -Int B when #isConcrete(I1) andBool notBool #isConcrete(B) andBool #isConcrete(I3)
    rule (I1 -Int B) +Int I3 => (I1 +Int I3) -Int B when #isConcrete(I1) andBool notBool #isConcrete(B) andBool #isConcrete(I3)

    rule I1 +Int (I2 +Int C) => (I1 +Int I2) +Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C)
    rule I1 +Int (I2 -Int C) => (I1 +Int I2) -Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C)
    rule I1 -Int (I2 +Int C) => (I1 -Int I2) -Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C)
    rule I1 -Int (I2 -Int C) => (I1 -Int I2) +Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C)

    rule I1 &Int (I2 &Int C) => (I1 &Int I2) &Int C when #isConcrete(I1) andBool #isConcrete(I2) andBool notBool #isConcrete(C)

    // 0xffff...f &Int N = N
    rule MASK &Int N => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK

    // N &Int 0xffff...f = N
    rule N &Int MASK => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK



    // for gas calculation
    rule A -Int (#if C #then B1 #else B2 #fi) => #if C #then (A -Int B1) #else (A -Int B2) #fi

    rule (#if C #then B1 #else B2 #fi) -Int A => #if C #then (B1 -Int A) #else (B2 -Int A) #fi
        when notBool #isConcrete(A) andBool #notKLabel(A, "#if_#then_#else_#fi_K-EQUAL")

    rule (#if C #then B1 #else B2 #fi) +Int A => #if C #then (B1 +Int A) #else (B2 +Int A) #fi








    rule X >Int Y => Y <Int X
    rule X >=Int Y => Y <=Int X

    rule notBool (X <Int Y) => Y <=Int X
    rule notBool (X <=Int Y) => Y <Int X








    rule bool2Word(A) |Int bool2Word(B) => bool2Word(A  orBool B)
    rule bool2Word(A) &Int bool2Word(B) => bool2Word(A andBool B)

    rule 1 |Int bool2Word(B) => 1
    rule 1 &Int bool2Word(B) => bool2Word(B)

    rule bool2Word(B) |Int 1 => 1
    rule bool2Word(B) &Int 1 => bool2Word(B)

    rule bool2Word(A)  ==K 0 => notBool(A)
    rule bool2Word(A)  ==K 1 => A
    rule bool2Word(A) =/=K 0 => A
    rule bool2Word(A) =/=K 1 => notBool(A)

    rule chop(bool2Word(B)) => bool2Word(B)

    rule #asWord(0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0
                   : 0 : 0 : 0 : 0 : 0 : 0 : 0 : 0 : nthbyteof(bool2Word( E ), I, N) : .WordStack)
         => bool2Word( E )





    rule 0 <=Int X &Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256
    rule         X &Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256

















    rule 0 <=Int nthbyteof(V, I, N)             => true
    rule         nthbyteof(V, I, N) <Int 256    => true
    rule         nthbyteof(V, I, N) <Int pow256 => true

    rule 0 <=Int #asWord(WS)          => true
    rule #asWord(WS) <Int pow256      => true

    rule 0 <=Int hash1(_)             => true
    rule         hash1(_) <Int pow256 => true

    rule 0 <=Int hash2(_,_)             => true
    rule         hash2(_,_) <Int pow256 => true

    rule 0 <=Int chop(V)             => true
    rule         chop(V) <Int pow256 => true

    rule 0 <=Int keccak(V)             => true
    rule         keccak(V) <Int pow256 => true

    rule 0 <=Int keccakIntList(_)             => true
    rule         keccakIntList(_) <Int pow256 => true












    rule X <=Int maxUInt256 => X <Int pow256
    rule X <=Int maxUInt160 => X <Int pow160
    rule X <=Int 255        => X <Int 256










    /*rule X <Int pow256 => true
      requires X <Int 256

    rule X <Int pow256 => true
      requires X <Int pow160

    rule 0 <=Int X => true
      requires 0 <Int X*/





    rule chop(I) => I requires 0 <=Int I andBool I <Int pow256







    syntax Bool ::= #notKLabel ( K , String ) [function]
    rule #notKLabel(T, L) => #getKLabelString(T) =/=String L orBool #isVariable(T)







    rule 0 <=Int #sizeWordStack ( _ , _ ) => true [smt-lemma]

endmodule


