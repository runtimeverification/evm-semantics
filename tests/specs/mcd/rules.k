requires "edsl.md"
requires "../lemmas.k"

module RULES
    imports EVM
    imports EDSL
    imports K-REFLECTION
    imports LEMMAS

// -*- mode: k3; -*-
// VERIFICATION.k

    rule #rangeUInt    (   1 ,      X ) => #range ( 0               <= X <= 1               ) [macro]

    rule bool2Word(notBool(A ==K 0)) => A
         requires #rangeUInt(1, A)

    //Blasphemy
    rule notBool(notBool(A)) => A

    rule ( WS1 ++ WS2 ) ++ WS3 => WS1 ++ ( WS2 ++ WS3 )


    // These rules exist in KEVM, but are marked [concrete].
    // Declared here to allow symbolic arguments.

    rule #lookup( (KEY |-> VAL) M, KEY ) => VAL
    rule #lookup(               M, KEY ) => 0 requires notBool KEY in_keys(M)

    rule #range(WM, START, WIDTH) => #range(WM, START +Int WIDTH -Int 1, WIDTH, .WordStack)

    rule WM[ N := W : WS     ] => (WM[N <- W])[N +Int 1 := WS]

    // We use #asByteStack to represet byte arrays rather than the #buf abstraction.
    // To enable this both #buf and #sizeByteArray must be symbolic.

    rule #buf(LEN, BYTES) => #padToWidth(LEN, #asByteStack( BYTES ))
    rule #sizeByteArray ( WS ) => #sizeWordStack(WS)

    // Operator direction normalization rules. Required to reduce the number of
    // forms of inequalities that can be matched by general lemmas. We chose to
    // keep <Int and <=Int because those operators are used in all range lemmas
    // and in #range macros. Operators >Int and >=Int are still allowed
    // anywhere except rules LHS. In all other places they will be matched and
    // rewritten by rules below.
    rule notBool (X <Int Y)  => Y <=Int X
    rule notBool (X <=Int Y) => Y <Int X
    rule notBool (X >Int Y)  => X <=Int Y
    rule notBool (X >=Int Y) => X <Int Y



rule ACCTCODE in SetItem( 1 )
                 SetItem ( 2 )
                 SetItem ( 3 )
                 SetItem ( 4 )
                 SetItem ( 5 )
                 SetItem ( 6 )
                 SetItem ( 7 )
                 SetItem ( 8 )
                 SetItem ( 9 )
                 => false
     requires ACCTCODE ==Int 0 orBool 10 <=Int ACCTCODE

    syntax IntList ::= bytesToWords ( WordStack )       [function]

    rule BS [0 .. M] [0 .. N ] => BS [ 0 .. N]
      requires N <=Int M

// --------------------------------------------------------------
    rule bytesToWords ( WS )
         => #asWord(#take(#sizeWordStack(WS) modInt 32, WS)) byteStack2IntList(#drop(#sizeWordStack(WS) modInt 32, WS))
         requires 0 <Int #sizeWordStack(WS) modInt 32

    rule bytesToWords ( WS ) => byteStack2IntList(WS)
         requires #sizeWordStack(WS) modInt 32 ==Int 0

// for terms came from bytecode not via #hashedLocation
    rule keccak(WS) => keccakIntList(bytesToWords(WS))
      requires ( notBool #isConcrete(WS) )

    rule 0 <=Int keccakIntList(N)     => true
    rule keccakIntList(N) <Int pow256 => true

   // for Vyper
    rule #padToWidth(N, #asByteStack(#asWord(WS))) => WS
      requires #sizeWordStack(WS) <=Int 32 andBool N ==Int #sizeWordStack(WS)

    // for Solidity
    rule #asWord(WS) /Int D => #asWord(#take(#sizeWordStack(WS) -Int log256Int(D), WS))
      requires D modInt 256 ==Int 0 andBool D >=Int 0
       andBool #sizeWordStack(WS) >=Int log256Int(D)
       andBool #sizeWordStack(WS) <=Int 32

    // for Solidity >= 0.5.6
    rule #asWord(WS) >>Int D => #asWord(#take(#sizeWordStack(WS) -Int (D /Int 8), WS))
     requires D modInt 8 ==Int 0 andBool D >=Int 0
       andBool #sizeWordStack(WS) >=Int (D /Int 8)
       andBool #sizeWordStack(WS) <=Int 32

    rule #sizeWordStack(#take(N, _)) => N
    rule #sizeWordStack(WS) >=Int 0 => true [smt-lemma]

    rule 0 +Int N => N
    rule N +Int 0 => N

    rule N -Int 0 => N

    rule 1 *Int N => N
    rule N *Int 1 => N
    rule 0 *Int _ => 0
    rule _ *Int 0 => 0

    rule N /Int 1 => N
    rule N *Int A /Int A => N

    rule 0 |Int N => N
    rule N |Int 0 => N
    rule N |Int N => N

    rule 0 &Int N => 0
    rule N &Int 0 => 0
    rule N &Int N => N

    rule N <<Int 0 => N
    rule N >>Int 0 => N

    rule (I1 +Int I2) +Int I3 => I1 +Int (I2 +Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 +Int I2) -Int I3 => I1 +Int (I2 -Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 -Int I2) +Int I3 => I1 -Int (I2 -Int I3) when #isConcrete(I2) andBool #isConcrete(I3)
    rule (I1 -Int I2) -Int I3 => I1 -Int (I2 +Int I3) when #isConcrete(I2) andBool #isConcrete(I3)

    rule I1 &Int (I2 &Int I3) => (I1 &Int I2) &Int I3 when #isConcrete(I1) andBool #isConcrete(I2)

    // 0xffff...f &Int N = N
    rule MASK &Int N => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK

    // 0xffff...f &Int N = N
    rule N &Int MASK => N  requires MASK ==Int (2 ^Int (log2Int(MASK) +Int 1)) -Int 1 // MASK = 0xffff...f
                            andBool 0 <=Int N andBool N <=Int MASK


    /// GAS Simplification
    rule (#if C #then B1 #else B2 #fi) >Int A => true
      requires B1 >Int A andBool B2 >Int A

    rule (#if C #then B1 #else B2 #fi) >=Int A => true
      requires B1 >=Int A andBool B2 >=Int A

    rule #if C #then (#if C #then B1 #else B2 #fi) -Int D #else (#if C #then B3 #else B4 #fi) -Int E #fi =>
         #if C #then B1 -Int D #else B4 -Int E #fi

    // avoid nested #ifte
    rule #if C1 #then A #else (B +Int #if C2 #then B2 #else B3 #fi) #fi =>
         #if C1 #then A #else B #fi +Int #if (C2 andBool notBool C1) #then B2 #else 0 #fi +Int #if ((notBool C2) andBool (notBool C1)) #then B3 #else 0 #fi

   //simplify trivial #ifs
   rule #if C1 #then A #else B #fi => A
      requires A ==K B

    rule #if C #then X +Int A #else X +Int B #fi => X +Int (#if C #then A #else B #fi)

    rule #if C #then (A +Int X) #else (B +Int X) #fi => ( #if C #then A #else B #fi ) +Int X

    rule #if C #then G -Int X #else G -Int Y #fi => G -Int (#if C #then X #else Y #fi)

    rule #if C #then X -Int G #else Y -Int G #fi => (#if C #then X #else Y #fi) -Int G

    rule #if C #then ((P -Int X) -Int A) #else ((Q -Int X) -Int B) #fi => (#if C #then (P -Int A) #else (Q -Int B) #fi) -Int X

    // SORT

    //    DIV
    rule  A -Int ( (B /Int 64)  +Int C) => (0 -Int ( (B /Int 64) -Int (A -Int C)))
      requires (notBool #isVariable(A))
      andBool (notBool #isConcrete(A))
      andBool (A =/=K (?D /Int 64))
    rule  A -Int ( (B /Int 64)  -Int C) => (0 -Int ( (B /Int 64) -Int (A +Int C)))
      requires (notBool #isVariable(A))
      andBool (notBool #isConcrete(A))
      andBool (A =/=K (?D /Int 64))
    rule  A +Int ( (B /Int 64) +Int  C) => (B /Int 64) +Int (A +Int  C)
      requires (notBool #isVariable(A))
      andBool (notBool #isConcrete(A))
      andBool (A =/=K (?D /Int 64))
    rule  A +Int ( (B /Int 64) -Int  C) => (B /Int 64) +Int (A -Int  C)
      requires (notBool #isVariable(A))
      andBool (notBool #isConcrete(A))
      andBool (A =/=K (?D /Int 64))


    /// ---


    rule A -Int A => 0

    rule bool2Word(A) |Int bool2Word(B) => bool2Word(A  orBool B)
    rule bool2Word(A) &Int bool2Word(B) => bool2Word(A andBool B)

    rule bool2Word(A)  ==K 0 => notBool(A)
    rule bool2Word(A)  ==K 1 => A

    rule 1 |Int bool2Word(X) => 1
    rule  bool2Word(X) |Int 1 => 1
    rule 1 &Int bool2Word(X) => bool2Word(X)
    rule bool2Word(X) &Int 1 => bool2Word(X)

    rule chop(bool2Word(B)) => bool2Word(B)





    rule 0 <=Int chop(V)             => true
    rule         chop(V) <Int pow256 => true

    rule 0 <=Int keccak(V)             => true
    rule         keccak(V) <Int pow256 => true

    rule 0 <=Int X &Int Y             => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256
    rule         X &Int Y <Int pow256 => true requires 0 <=Int X andBool X <Int pow256 andBool 0 <=Int Y andBool Y <Int pow256





    rule chop(I) => I requires 0 <=Int I andBool I <Int pow256




rule chop(#unsigned(W)) => #unsigned(W)
  requires #rangeSInt(256, W)

rule #signed(#unsigned(W)) => W
  requires #rangeSInt(256, W)

rule #unsigned(#signed(W)) => W
  requires #rangeUInt(256, W)

rule W0 s<Word W1 => #signed(W0) <Word #signed(W1)

rule   #signed(X) ==K   #signed(Y) => X ==K Y requires #rangeUInt(256,X) orBool #rangeUInt(256,Y)
rule #unsigned(X) ==K #unsigned(Y) => X ==K Y requires #rangeSInt(256,X) orBool #rangeSInt(256,Y)


rule A modInt pow160 => A
  requires #rangeAddress(A)

syntax Bool ::= #notPrecompileAddress ( Int ) [function]
// ---------------------------------------
rule #notPrecompileAddress ( X ) => 0 ==Int X orBool (10 <=Int X andBool #rangeAddress(X))

// New addresses are not precompiles

rule #newAddr(A, B, C) in #precompiledAccounts(SCHED) => false
rule #newAddr(A, B) in #precompiledAccounts(SCHED) => false

// New addresses are not zero

rule #newAddr(A, B, C) ==K 0 => false
rule #newAddr(A, B) ==K 0 => false
rule 0 ==K #newAddr(A, B, C) => false
rule 0 ==K #newAddr(A, B) => false

//RULES MUST USE ==K and not ==Int
//Warning: assumes injective hashing

rule keccakIntList(A B .IntList) ==K keccakIntList(C D .IntList) => A ==Int C andBool B ==Int D

rule keccakIntList(A B C .IntList) ==K keccakIntList(D E F .IntList) => A ==Int D andBool B ==Int E andBool C ==Int F


rule keccakIntList(C) ==K A => false
     requires 0 <=Int A andBool A <=Int 20

rule keccakIntList(C) +Int B ==K A => false
     requires 0 <=Int A andBool A <=Int 20
     andBool 0 <=Int B andBool B <=Int 20

rule A ==K keccakIntList(C) +Int B => false
     requires 0 <=Int A andBool A <=Int 20
     andBool 0 <=Int B andBool B <=Int 20

rule keccakIntList(C) +Int B ==K keccakIntList(A) => false
     requires 0 <=Int B andBool B <=Int 20

rule keccakIntList(A) +Int B ==K keccakIntList(A) +Int C => false
     requires B =/=Int C

rule keccakIntList(A) +Int B ==K keccakIntList(C) +Int D => false
     requires B =/=K C


rule keccakIntList(A) ==K keccakIntList(C) +Int B => false
     requires 0 <=Int B andBool B <=Int 20


rule A ==K keccakIntList(C) => false
     requires 0 <=Int A andBool A <=Int 20

//Symbolic wrapper over the argument of #ecrec, no implementation.
//                         hash v  r   s
syntax Int ::= #symEcrec ( Int , Int , Int , Int ) [function]

rule <k> ECREC => #end EVMC_SUCCESS ... </k>
       <callData> DATA </callData>
       <output> _ => #ecrec(#symEcrec(#asWord(#take(32, DATA)), #asWord(#take(32, #drop(32, DATA))), #asWord(#take(32, #drop(64, DATA))), #asWord(#take(32, #drop(96, DATA))))) </output>
    requires notBool #isConcrete(DATA) andBool #sizeWordStack(DATA) ==Int 128
[trusted]

rule #memoryUsageUpdate(MU, START, WIDTH) => maxInt(MU, (START +Int WIDTH) up/Int 32) requires WIDTH  >Int 0


// ./src/storage.k.md

syntax Int::= "#DssCdpManager.vat" [function]
rule #DssCdpManager.vat => 0

syntax Int::= "#DssCdpManager.cdpi" [function]
rule #DssCdpManager.cdpi => 1

syntax Int ::= "#DssCdpManager.urns" "[" Int "]" [function]
rule #DssCdpManager.urns[Cdp] => #hashedLocation("Solidity", 2, Cdp)

syntax Int ::= "#DssCdpManager.list" "[" Int "].prev" [function]
rule #DssCdpManager.list[Usr].prev => #hashedLocation("Solidity", 3, Usr)

syntax Int ::= "#DssCdpManager.list" "[" Int "].next" [function]
rule #DssCdpManager.list[Usr].next => #hashedLocation("Solidity", 3, Usr) +Int 1

syntax Int ::= "#DssCdpManager.owns" "[" Int "]" [function]
rule #DssCdpManager.owns[Cdp] => #hashedLocation("Solidity", 4, Cdp)

syntax Int ::= "#DssCdpManager.ilks" "[" Int "]" [function]
rule #DssCdpManager.ilks[Cdp] => #hashedLocation("Solidity", 5, Cdp)

syntax Int ::= "#DssCdpManager.first" "[" Int "]" [function]
rule #DssCdpManager.first[Usr] => #hashedLocation("Solidity", 6, Usr)

syntax Int ::= "#DssCdpManager.last" "[" Int "]" [function]
rule #DssCdpManager.last[Usr] => #hashedLocation("Solidity", 7, Usr)

syntax Int ::= "#DssCdpManager.count" "[" Int "]" [function]
rule #DssCdpManager.count[Usr] => #hashedLocation("Solidity", 8, Usr)

syntax Int ::= "#DssCdpManager.cdpCan" "[" Int "][" Int "][" Int "]" [function]
rule #DssCdpManager.cdpCan[Own][Cdp][Usr] => #hashedLocation("Solidity", 9, Own Cdp Usr)

syntax Int ::= "#DssCdpManager.urnCan" "[" Int "][" Int "]" [function]
rule #DssCdpManager.urnCan[Urn][Usr] => #hashedLocation("Solidity", 10, Urn Usr)

syntax Int ::= "#Vat.wards" "[" Int "]" [function]
rule #Vat.wards[A] => #hashedLocation("Solidity", 0, A)

syntax Int ::= "#Vat.can" "[" Int "][" Int "]" [function]
rule #Vat.can[A][B] => #hashedLocation("Solidity", 1, A B)

syntax Int ::= "#Vat.ilks" "[" Int "].Art" [function]
rule #Vat.ilks[Ilk].Art => #hashedLocation("Solidity", 2, Ilk) +Int 0

syntax Int ::= "#Vat.ilks" "[" Int "].rate" [function]
rule #Vat.ilks[Ilk].rate => #hashedLocation("Solidity", 2, Ilk) +Int 1

syntax Int ::= "#Vat.ilks" "[" Int "].spot" [function]
rule #Vat.ilks[Ilk].spot => #hashedLocation("Solidity", 2, Ilk) +Int 2

syntax Int ::= "#Vat.ilks" "[" Int "].line" [function]
rule #Vat.ilks[Ilk].line => #hashedLocation("Solidity", 2, Ilk) +Int 3

syntax Int ::= "#Vat.ilks" "[" Int "].dust" [function]
rule #Vat.ilks[Ilk].dust => #hashedLocation("Solidity", 2, Ilk) +Int 4

syntax Int ::= "#Vat.urns" "[" Int "][" Int "].ink" [function]
rule #Vat.urns[Ilk][Usr].ink => #hashedLocation("Solidity", 3, Ilk Usr)

syntax Int ::= "#Vat.urns" "[" Int "][" Int "].art" [function]
rule #Vat.urns[Ilk][Usr].art => #hashedLocation("Solidity", 3, Ilk Usr) +Int 1

syntax Int ::= "#Vat.gem" "[" Int "][" Int "]" [function]
rule #Vat.gem[Ilk][Usr] => #hashedLocation("Solidity", 4, Ilk Usr)

syntax Int ::= "#Vat.dai" "[" Int "]" [function]
rule #Vat.dai[A] => #hashedLocation("Solidity", 5, A)

syntax Int ::= "#Vat.sin" "[" Int "]" [function]
rule #Vat.sin[A] => #hashedLocation("Solidity", 6, A)

syntax Int ::= "#Vat.debt" [function]
rule #Vat.debt => 7

syntax Int ::= "#Vat.vice" [function]
rule #Vat.vice => 8

syntax Int ::= "#Vat.Line" [function]
rule #Vat.Line => 9

syntax Int ::= "#Vat.live" [function]
rule #Vat.live => 10
// ./src/lemmas.k.md

syntax Int ::= num0 ( Int ) [function, smtlib(smt_num0)]
syntax Int ::= num1 ( Int ) [function, smtlib(smt_num1)]

rule num0(N) >=Int 0 => num0(N) >=Int 1
  requires N >=Int 1
  andBool N modInt 2 ==Int 0

rule num1(N) >=Int 0 => num1(N) >=Int 1
  requires N >Int 1
  andBool N modInt 2 =/=Int 0

rule num0(N /Int 2) => num0(N) -Int 1
  requires N >=Int 1
  andBool N modInt 2 ==Int 0

rule num0(N /Int 2) => num0(N)
  requires N >=Int 1
  andBool N modInt 2 ==Int 1

rule num1(N /Int 2) => num1(N) -Int 1
  requires N >Int 1
  andBool N modInt 2 ==Int 1

rule num1(N /Int 2) => num1(N)
  requires N >Int 1
  andBool N modInt 2 ==Int 0

rule num0(N) => 0
  requires N ==Int 1

rule num1(N) => 0
  requires N ==Int 1

rule (#if C #then A #else B #fi *Int X) <=Int maxUInt256 => true
  requires A *Int X <=Int maxUInt256
  andBool B *Int X <=Int maxUInt256
syntax Int ::= "pow48"  [function]
syntax Int ::= "pow208" [function]
rule pow48  => 281474976710656                                                 [macro]
rule pow208 => 411376139330301510538742295639337626245683966408394965837152256 [macro]

syntax Int ::= "#WordPackUInt48UInt48" "(" Int "," Int ")" [function]
// ----------------------------------------------------------
rule #WordPackUInt48UInt48(X, Y) => Y *Int pow48 +Int X
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

syntax Int ::= "#WordPackAddrUInt48UInt48" "(" Int "," Int "," Int ")" [function]
// ----------------------------------------------------------------------
rule #WordPackAddrUInt48UInt48(A, X, Y) => Y *Int pow208 +Int X *Int pow160 +Int A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

syntax Int ::= "#WordPackAddrUInt8" "(" Int "," Int ")" [function]
// ----------------------------------------------------------
rule #WordPackAddrUInt8(X, Y) => Y *Int pow160 +Int X
  requires #rangeAddress(X)
  andBool #rangeUInt(8, Y)

syntax Int ::= "#string2Word" "(" String ")" [function]
// ----------------------------------------------------
rule #string2Word(S) => #asWord(#padRightToWidth(32, #parseByteStackRaw(S)))
syntax Int ::= "#Wad" [function]
// -----------------------------
rule #Wad => 1000000000000000000           [macro]

syntax Int ::= "#Ray" [function]
// -----------------------------
rule #Ray => 1000000000000000000000000000  [macro]

syntax Int ::= "#rmul" "(" Int "," Int ")" [function]
rule #rmul(X, Y) => (X *Int Y) /Int #Ray
syntax Int ::= "#rpow" "(" Int "," Int "," Int "," Int ")"  [function, smtlib(smt_rpow), smt-prelude]

syntax Int ::= "#ifInt" Bool "#then" Int "#else" Int "#fi" [function, smtlib(ite), hook(KEQUAL.ite)]

rule A *Int C /Int C => A
  requires A *Int C <Int pow256

rule (X *Int Y) /Word Y => #ifInt Y ==Int 0 #then 0 #else chop(X) #fi

rule A /Int B <Int pow256 => true
  requires A <Int pow256

rule Z *Int (X ^Int N) => Z
  requires N ==Int 0

rule Z *Int (X ^Int (N %Int 2)) => Z
  requires N ==Int 0

rule 0 ^Int N => 1
  requires N ==Int 0

rule 0 ^Int N => 0
  requires N >Int 0

rule 0 <=Int (N /Int 2) => true
  requires 0 <=Int N

rule N /Int 2 <Int pow256 => true
  requires N <Int pow256

// TODO - review - do i need it?
rule chop(X *Int X) => X *Int X
  requires #rpow(Z, X, N, B) *Int B <Int pow256
  andBool N >=Int 2


rule #rpow(Z, X, 0, Base) => Z

rule #rpow(Z, X, N, Base) => Z
  requires N modInt 2 ==Int 0
  andBool N /Int 2 ==Int 0

rule #rpow(Z, 0, N, Base) => 0

rule #rpow(Base, X, N, Base) => X
  requires N ==Int 1

rule #rpow(((Z *Int X) +Int Half) /Int Base, X, N /Int 2, Base) =>
     #rpow(Z,                                 X, N,       Base)
  requires Half ==Int Base /Int 2
  andBool  N ==Int 1

rule #rpow(((Z *Int X) +Int Half) /Int Base, ((X *Int X) +Int Half) /Int Base, N /Int 2, Base) =>
     #rpow( Z                               , X                               , N       , Base )
  requires N modInt 2 =/=Int 0
  andBool  N >=Int 2
  andBool Half ==Int Base /Int 2

rule #rpow( Z                              , ((X *Int X) +Int Half) /Int Base, N /Int 2, Base) =>
     #rpow( Z                              , X                               , N       , Base )
  requires N modInt 2 ==Int 0
  andBool  N >=Int 2
andBool Half ==Int Base /Int 2

rule #rpow( X                              , ((X *Int X) +Int Half) /Int Base, N /Int 2, Base) =>
     #rpow( Base                           , X                               , N       , Base )
  requires N modInt 2 =/=Int 0
  andBool  N /Int 2 =/=Int 0
  andBool  Half ==Int Base /Int 2

rule Z *Int X <Int pow256 => true
  requires #rpow(Z, X, N, Base) <Int pow256
// hashed storage offsets never overflow (probabilistic assumption):
rule chop(keccakIntList(L) +Int N) => keccakIntList(L) +Int N
  requires N <=Int 100

// solidity also needs:
rule chop(keccakIntList(L)) => keccakIntList(L)
// and
rule chop(N +Int keccakIntList(L)) => keccakIntList(L) +Int N
  requires N <=Int 100
syntax Int ::= "Mask12_32" [function]
syntax Int ::= "Mask0_6" [function]
syntax Int ::= "Mask6_12" [function]
syntax Int ::= "Mask0_12" [function]
syntax Int ::= "Mask0_26" [function]
syntax Int ::= "Mask26_32" [function]
syntax Int ::= "Mask20_26" [function]
// -----------------------------------
// 0x000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffff
rule Mask0_6 => 411376139330301510538742295639337626245683966408394965837152255                  [macro]
// 0xffffffffffff000000000000ffffffffffffffffffffffffffffffffffffffff
rule Mask6_12 => 115792089237315784047431654708638870748305248246218003188207458632603225030655 [macro]
// 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff
rule Mask0_12 => 1461501637330902918203684832716283019655932542975                               [macro]
// 0xffffffffffffffffffffffff0000000000000000000000000000000000000000
rule Mask12_32 => 115792089237316195423570985007226406215939081747436879206741300988257197096960 [macro]
// 0x0000000000000000000000000000000000000000000000000000ffffffffffff
rule Mask0_26 => 281474976710655                                                                 [macro]
// 0xffffffffffffffffffffffffffffffffffffffff000000000000ffffffffffff
rule Mask20_26 => 115792089237316195423570985008687907853269984665561335876943319951794562400255 [macro]
// 0xffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000
rule Mask26_32 => 115792089237316195423570985008687907853269984665640564039457583726438152929280 [macro]

syntax Int ::= "maxUInt208" [function]
rule maxUInt208 => 411376139330301510538742295639337626245683966408394965837152255 [macro]

rule maxUInt208 &Int ((X *Int pow208) +Int A ) => A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)

rule (X *Int pow208) |Int A => (X *Int pow208 +Int A)
  requires #rangeUInt(48, X)
  andBool #rangeAddress(A)

rule Mask26_32 &Int (Y *Int pow48 +Int X) => Y *Int pow48
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule Mask20_26 &Int (Y *Int pow48 +Int X) => X
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule X |Int Y *Int pow48 => Y *Int pow48 +Int X
  requires #rangeUInt(48, Y)
  andBool #rangeUInt(48, X)

rule (X *Int pow48) |Int Y => (X *Int pow48) +Int Y
  requires #rangeUInt(48, Y)
  andBool #rangeUInt(48, X)

rule Mask12_32 &Int A => 0
  requires #rangeAddress(A)

rule X |Int 0 => X

rule chop(A &Int B) => A &Int B
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

rule chop(A |Int B) => A |Int B
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

// Masking for packed words
rule Mask12_32 &Int (Y *Int pow208 +Int (X *Int pow160 +Int A)) => Y *Int pow208 +Int X *Int pow160
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule B |Int (Y *Int pow208 +Int X *Int pow160) => Y *Int pow208 +Int X *Int pow160 +Int B
  requires #rangeAddress(B)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule (Y *Int pow208 +Int ( X *Int pow160 +Int A ) ) /Int pow208 => Y
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule (Y *Int pow48 +Int X) /Int pow48 => Y
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule Mask0_6 &Int (X *Int pow208 +Int ( Y *Int pow160 +Int A ) ) => Y *Int pow160 +Int A
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)
  andBool #rangeAddress(A)

rule Mask6_12 &Int (Y *Int pow208 +Int ( X *Int pow160 +Int A) ) => Y *Int pow208 +Int A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule (Y *Int pow208) |Int (X *Int pow160 +Int A) => Y *Int pow208 +Int X *Int pow160 +Int A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule (X *Int pow160) |Int (Y *Int pow208 +Int A) => Y *Int pow208 +Int X *Int pow160 +Int A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule maxUInt160 &Int ((X *Int pow208) +Int ((Y *Int pow160) +Int A)) => A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule maxUInt160 &Int ((X *Int pow208) +Int (Y *Int pow160)) => 0
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule maxUInt160 &Int ((X *Int pow208) +Int A) => A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)

rule maxUInt160 &Int ((X *Int pow160) +Int A) => A
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)

rule maxUInt160 &Int (X *Int pow208) => 0
  requires #rangeUInt(48, X)

rule maxUInt160 &Int (X *Int pow160) => 0
  requires #rangeUInt(48, X)

rule (((X *Int pow208) +Int ( (Y *Int pow160) +Int A)) /Int pow160) => (X *Int pow48) +Int Y
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule maxUInt48 &Int (X *Int pow48) +Int Y => Y
  requires #rangeUInt(48, X)
  andBool #rangeUInt(48, Y)

rule ((X *Int pow208) +Int A) /Int pow160 => X *Int pow48
  requires #rangeAddress(A)
  andBool #rangeUInt(48, X)

rule ((X *Int pow160) +Int A) /Int pow160 => X
  requires #rangeAddress(A)

rule (Y *Int pow208 +Int X *Int pow160) /Int pow208 => Y
  requires #rangeUInt(48, X)

rule (Y *Int pow208 +Int A) /Int pow208 => Y
  requires #rangeAddress(A)

rule maxUInt48 &Int (X *Int pow48) => 0
  requires #rangeUInt(48, X)
rule WS ++ .WordStack => WS

rule #sizeWordStack ( #padToWidth ( 32 , #asByteStack ( #unsigned ( W ) ) ) ) => 32
  requires #rangeSInt(256, W)

// custom ones:
rule #asWord(#padToWidth(32, #asByteStack(#unsigned(X)))) => #unsigned(X)
  requires #rangeSInt(256, X)

// rule #take(N, #padToWidth(N, WS) ++ WS' ) => #padToWidth(N, WS)

rule #take(N, #padToWidth(N, WS) ) => #padToWidth(N, WS)
rule notBool((Mask0_26 &Int (A +Int B)) <Int A) => A +Int B <=Int maxUInt48
  requires #rangeUInt(48, A)
  andBool #rangeUInt(48, B)
rule #unsigned(X) ==K 0 => X ==Int 0
  requires #rangeSInt(256, X)

// addui
// lemmas for sufficiency
rule chop(A +Int #unsigned(B)) => A +Int B
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeUInt(256, A +Int B)

rule A <=Int chop(A +Int #unsigned(B)) => A +Int B <=Int maxUInt256
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool 0 <Int B

rule chop(A +Int #unsigned(B)) <=Int A => 0 <=Int A +Int B
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool B <Int 0

// subui
// lemmas for sufficiency
rule A -Word #unsigned(B) => A -Int B
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeUInt(256, A -Int B)

 rule A -Word #unsigned(B) <=Int A => minUInt256 <=Int A -Int B
   requires #rangeUInt(256, A)
   andBool #rangeSInt(256, B)
   andBool 0 <=Int B

 rule A <Int A -Word #unsigned(B) => A -Int B <=Int maxUInt256
   requires #rangeUInt(256, A)
   andBool #rangeSInt(256, B)
   andBool B <Int 0

rule A -Word #unsigned(B) <Int A => maxUInt256 <Int A -Int B
   requires #rangeUInt(256, A)
   andBool #rangeSInt(256, B)
   andBool B <Int 0

rule (A +Int pow256) -Int #unsigned(B) => A -Int B
   requires #rangeUInt(256, A)
   andBool #rangeSInt(256, B)
   andBool #rangeUInt(256, A -Int B)
   andBool B <Int 0

// mului
// lemmas for sufficiency
rule A *Int #unsigned(B) => #unsigned(A *Int B)
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeSInt(256, A *Int B)

rule abs(#unsigned(A *Int B)) /Int abs(#unsigned(B)) => A
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool #rangeSInt(256, A *Int B)
  andBool notBool (#unsigned(B) ==Int 0)


rule abs(B) ==K 0 => B ==K 0

rule #sgnInterp(sgn(#unsigned(A *Int B)) *Int sgn(#unsigned(B)), A) => A
  requires #rangeSInt(256, A *Int B)
  andBool #rangeUInt(256, A)
  andBool #rangeSInt(256, B)

// lemmas for necessity
rule #signed(X) <Int 0 => notBool #rangeSInt(256, X)
   requires #rangeUInt(256, X)

rule (chop(A *Int B) /Int B ==K A) => #rangeUInt(256, A *Int B)
  requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

rule (#sgnInterp(sgn(chop(A *Int #unsigned(B))) *Int sgn(#unsigned(B)), abs(chop(A *Int #unsigned(B))) /Int abs(#unsigned(B))) ==K A) => #rangeSInt(256, A *Int B)
  requires #rangeUInt(256, A)
  andBool #rangeSInt(256, B)
  andBool B =/=Int 0

rule 0 -Word X => #unsigned(0 -Int X)
  requires 0 <=Int X andBool X <=Int pow255
/*
  proof:

  1) rule W0 -Word W1 => chop( (W0 +Int pow256) -Int W1 ) requires W0 <Int W1
  2) rule chop ( I:Int ) => I modInt pow256 [concrete, smt-lemma]
  3) rule W0 -Word W1 => chop( W0 -Int W1 ) requires W0 >=Int W1

  Assume X != 0:

  0 < X                   : 0 -W X =(1)=> chop( pow256 - X )
  0 < pow256 - X < pow256 : chop( pow256 - X ) =(2)=> pow256 - X

  Assume X == 0:

  0 == X                  : 0 -W 0 =(3)=> chop( 0 - 0 )
*/

rule #range(WS [ X := #padToWidth(32, Y) ], Z, 32, WSS) => #range(WS, Z, 32, WSS)
  requires Z +Int 32 <Int X

// possibly wrong but i'll keep using it as a hack
rule #sizeWordStack(#range(WS, Y, Z, WSS)) => Z

//assume ecrec returns an address
rule maxUInt160 &Int #symEcrec(MSG, V, R, S) => #symEcrec(MSG, V, R, S)

    rule 0 <=Int #symEcrec(MSG, V, R, S)             => true
    rule         #symEcrec(MSG, V, R, S) <Int pow256 => true

rule A -Word B <=Int A => 0 <=Int A -Int B
 requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

rule A <=Int chop(A +Int B) => A +Int B <=Int maxUInt256
 requires #rangeUInt(256, A)
  andBool #rangeUInt(256, B)

rule #sgnInterp(sgn(chop(A *Int #unsigned(B))) *Int -1, abs(chop(A *Int #unsigned(B))) /Int (pow256 -Int #unsigned(B))) ==K A => #rangeSInt(256, A *Int B)
 requires #rangeUInt(256, A)
 andBool #rangeSInt(256, B)
 andBool B <Int 0

rule #sgnInterp(sgn(chop(A *Int #unsigned(B))), abs(chop(A *Int #unsigned(B))) /Int #unsigned(B)) ==K A => #rangeSInt(256, A *Int B)
 requires #rangeUInt(256, A)
 andBool #rangeSInt(256, B)
 andBool 0 <Int B

// Lemmas for Vat_frob_fail
rule A +Int #unsigned(B) => A +Int B
  requires #rangeUInt(256, A)
  andBool  #rangeUInt(256, B)
  andBool  #rangeUInt(256, A +Int B)

rule A +Int #unsigned(B) => A
  requires B ==K 0

// lemma for Jug_drip
rule A -Word B => #unsigned(A -Int B)
 requires #rangeSInt(256, A)
  andBool #rangeSInt(256, B)
  andBool 0 <=Int B
  andBool 0 <=Int A

// lemmas for End_skim
rule (A +Int (0 -Int B)) => A -Int B
rule (A *Int (0 -Int B)) => (0 -Int (A *Int B))
rule (A -Int (0 -Int B)) => A +Int B
//lemmas for End_bail
rule (0 -Int A) <Int B => (0 -Int B) <Int A
  requires (notBool #isConcrete(A))
  andBool #isConcrete(B)
rule (0 -Int A) <=Int B => (0 -Int B) <=Int A
  requires (notBool #isConcrete(A))
  andBool #isConcrete(B)
rule A <=Int (0 -Int B) => B <=Int 0 -Int A
  requires (notBool #isConcrete(B))
  andBool #isConcrete(A)
rule A <Int (0 -Int B) => B <Int 0 -Int A
  requires (notBool #isConcrete(B))
  andBool #isConcrete(A)

// Lemmas dealing with stupid 0
rule (0 -Int X) *Int Y => 0 -Int (X *Int Y)
rule (0 -Int X) /Int Y => 0 -Int (X /Int Y)

rule #unsigned( X *Int Y ) /Int #unsigned( Y ) => X
  requires #rangeSInt(256, X *Int Y)
  andBool #rangeSInt(256, X)
  andBool #rangeSInt(256, Y)
  andBool 0 <=Int X
  andBool 0 <Int Y

rule A +Int B => A
  requires B ==K 0
  andBool #isVariable(A)
  andBool #isVariable(B)

rule A +Int B => B
  requires A ==K 0
  andBool #isVariable(A)
  andBool #isVariable(B)

// lemma for Cat_bite-full to prevent unsigned(0 - X) devision
rule pow256 -Int #unsigned(0 -Int X) => X
  requires X >Int 0


// lemma to deal with deep nested calls - gas stuff
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (A14 +Int (A15 +Int (A16 +Int (A17 +Int (X +Int AS)))))))))))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (A14 +Int (A15 +Int (A16 +Int (A17 +Int AS)))))))))))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (A14 +Int (A15 +Int (A16 +Int (X +Int AS))))))))))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (A14 +Int (A15 +Int (A16 +Int AS))))))))))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (A14 +Int (A15 +Int (X +Int AS)))))))))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (A14 +Int (A15 +Int AS)))))))))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (A14 +Int (X +Int AS))))))))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (A14 +Int AS))))))))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int (X +Int AS)))))))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (A13 +Int AS)))))))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int (X +Int AS))))))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (A12 +Int AS))))))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int (X +Int AS)))))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (A11 +Int AS)))))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int (X +Int AS))))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (A10 +Int AS))))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int (X +Int AS)))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (A9 +Int AS)))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int (X +Int AS))))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (A8 +Int AS))))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int (X +Int AS)))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (A7 +Int AS)))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int (X +Int AS))))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (A6 +Int AS))))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int (X +Int AS)))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (A5 +Int AS)))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int (X +Int AS))))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int (A4 +Int AS))))
rule X -Int (A1 +Int (A2 +Int (A3 +Int (X +Int AS)))) => 0 -Int (A1 +Int (A2 +Int (A3 +Int AS)))
rule X -Int (A1 +Int (A2 +Int (X +Int AS))) => 0 -Int (A1 +Int (A2 +Int AS))

// Vat_fork-same_fail lemma
rule X +Int (pow256 -Int #unsigned(Y)) => X -Int Y
  requires Y <Int 0
  andBool  0 <=Int X -Int Y

rule #unsigned(X) -Int (pow256 +Int X) => 0
  requires X <Int 0

// skim/bail Rate * Art <= pow255 (condition for grab)
rule #signed(chop((A *Int #unsigned((0 -Int B))))) <=Int 0 => #rangeSInt(256, 0 -Int (A *Int B))
  requires #rangeUInt(256, A)
  andBool 0 <Int B
  andBool #rangeSInt(256, 0 -Int B)
syntax Int ::= "keccak30"
syntax Int ::= "keccak30PlusOne"
rule keccak30 => 24465873643947496235832446106509767096567058095563226156125564318740882468607 [macro]
rule keccak30PlusOne => 24465873643947496235832446106509767096567058095563226156125564318740882468608 [macro]

rule keccakIntList(C) +Int B ==K keccak30 => false
  requires 0 <=Int B andBool B <=Int 20
  andBool C =/=K (3 0 .IntList)

rule keccak30 ==K keccakIntList(C) +Int B => false
  requires 0 <=Int B andBool B <=Int 20
  andBool C =/=K (3 0 .IntList)

rule keccakIntList(C) ==K keccak30 => false
  requires C =/=K (3 0 .IntList)

rule keccak30 ==K keccakIntList(C) => false
  requires C =/=K (3 0 .IntList)

rule keccakIntList(C) ==K keccak30PlusOne => false

rule keccak30PlusOne ==K keccakIntList(C) => false

rule WM [ N := #take(I, W) ] => (WM [ N := (W [ 0 ] : .WordStack) ]) [ (N +Int 1) := (#take(I -Int 1, #drop(1, W))) ]
  requires I >=Int 1

rule WM [ N := #take(I, #drop(J, W)) ] => WM [ N := (W [ J ] : .WordStack) ] [ (N +Int 1) := (#take(I -Int 1, #drop(J +Int 1, W))) ]
  requires I >=Int 1

endmodule
