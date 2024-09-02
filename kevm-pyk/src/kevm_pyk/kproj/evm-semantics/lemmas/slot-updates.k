requires "word.md"

module SLOT-UPDATES [symbolic]
    imports EVM-TYPES
    imports BUF
    imports WORD

    // ###########################################################################
    // Auxiliaries
    // ###########################################################################

    // Index of first bit that equals one
    syntax Int ::=  #getFirstOneBit(Int) [function, total]

    rule [gfo-succ]: #getFirstOneBit(X:Int) => log2Int ( X &Int ( ( maxUInt256 xorInt X ) +Int 1 ) ) requires #rangeUInt(256, X) andBool X =/=Int 0 [preserves-definedness]
    rule [gfo-fail]: #getFirstOneBit(_:Int) => -1                                                    [owise]

    // Index of first bit that equals zero
    syntax Int ::= #getFirstZeroBit(Int) [function, total]

    rule [gfz-succ]: #getFirstZeroBit(X:Int) => #getFirstOneBit ( maxUInt256 xorInt X ) requires #rangeUInt(256, X) [preserves-definedness]
    rule [gfz-fail]: #getFirstZeroBit(_:Int) => -1                                      [owise]

    // Slot updates are performed by the compiler with the help of masks,
    // which are 256-bit integers of the form 11111111100000000000111111111111111
    //                                                 |- WIDTH -||-   SHIFT   -|

    // Shift of a mask, in bits and in bytes
    syntax Int ::= #getMaskShiftBits(Int)  [function, total]
    syntax Int ::= #getMaskShiftBytes(Int) [function, total]

    rule [gms-bits]: #getMaskShiftBits(X:Int) => #getFirstZeroBit(X)

    rule [gms-bits-succ]: #getMaskShiftBytes(X:Int) => #getFirstZeroBit(X) /Int 8 requires #getMaskShiftBits(X) modInt 8 ==Int 0 [preserves-definedness]
    rule [gms-bits-fail]: #getMaskShiftBytes(_:Int) => -1                         [owise]

    // Width of a mask, in bits and in bytes
    syntax Int ::= #getMaskWidthBits(Int)  [function, total]
    syntax Int ::= #getMaskWidthBytes(Int) [function, total]

    rule [gmw-bits-succ-1]: #getMaskWidthBits(X:Int) => 256 -Int #getMaskShiftBits(X:Int)             requires  0 <=Int #getMaskShiftBits(X) andBool 0 ==Int X >>Int #getMaskShiftBits(X) [preserves-definedness]
    rule [gmw-bits-succ-2]: #getMaskWidthBits(X:Int) => #getFirstOneBit(X >>Int #getMaskShiftBits(X)) requires  0 <=Int #getMaskShiftBits(X) andBool 0  <Int X >>Int #getMaskShiftBits(X) [preserves-definedness]
    rule [gmw-bits-fail]:   #getMaskWidthBits(_:Int) => -1                                            [owise]

    rule [gmw-bytes-succ]: #getMaskWidthBytes(X:Int) => #getMaskWidthBits(X) /Int 8 requires #getMaskWidthBits(X) modInt 8 ==Int 0 [preserves-definedness]
    rule [gmw-bytes-fail]: #getMaskWidthBytes(_:Int) => -1                          [owise]

    // Mask recogniser
    syntax Bool ::= #isMask(Int) [function, total]

    // A number is a mask if it has a valid shift, and a valid width, and all remaining bits set to one
    rule [is-mask-true]:
      #isMask(X:Int) => maxUInt256 ==Int X |Int ( 2 ^Int ( #getMaskShiftBits(X) +Int #getMaskWidthBits(X) ) -Int 1 )
        requires 0 <=Int #getMaskShiftBytes(X) andBool 0 <=Int #getMaskWidthBytes(X)
        [preserves-definedness]

    // and is not a mask otherwise
    rule [is-mask-false]: #isMask(_:Int) => false [owise]

    // Shift recogniser
    syntax Bool ::= #isByteShift(Int) [function, total]

    // A number is a shift if it is non-zero, in the Word range, and a power of two divisible by 8
    rule #isByteShift(X) => X ==Int 2 ^Int log2Int(X) andBool log2Int(X) modInt 8 ==Int 0 requires 0 <Int X andBool X <Int pow256 [preserves-definedness]
    rule #isByteShift(_) => false                                                         [owise]

    // ###########################################################################
    // Masking lemmas
    // ###########################################################################

    // Slot updates are of the general form (SHIFT *Int VALUE) |Int (MASK &Int #asWord( SLOT:Bytes )),
    // where the masking clears the part of the slot into which VALUE will be stored,
    // and for VALUE to be stored correctly it first has to be shifted appropriately.
    // Note that SHIFT and MASK are always concrete.
    //
    // We perform this update in several stages:
    // 1. First, we simplify MASK &Int #asWord( SLOT ), which results in
    //    ( VALUE *Int SHIFT ) |Int #asWord ( B1 +Bytes ... +Bytes BN ).
    // 2. Then, we isolate the +Bytes-junct(s) that will be overwritten.
    // 3. Then, we write the VALUE, possibly splitting the identified +Bytes-junct(s).
    //
    // Note that we require additional simplifications to account for the fact that
    // VALUE and SLOT can also be concrete. In the former case, we need to extract the
    // SHIFT appropriate, and in the latter case, the slot will appear on the LHS of the |Int.

    // 1. Slot masking using &Int
    rule [mask-b-and]:
      MASK:Int &Int SLOT:Int =>
        #asWord ( #buf ( 32, SLOT ) [ 32 -Int ( #getMaskShiftBytes(MASK) +Int #getMaskWidthBytes(MASK) ) := #buf ( #getMaskWidthBytes(MASK), 0 ) ] )
        requires #isMask(MASK) andBool #rangeUInt(256, SLOT)
        [simplification, concrete(MASK), preserves-definedness]

    // 2a. |Int and +Bytes, update to be done in left
    rule [bor-update-to-left]:
      A |Int #asWord ( B1 +Bytes B2 ) =>
        #asWord ( #buf ( 32 -Int lengthBytes(B2), (A /Int (2 ^Int (8 *Int lengthBytes(B2)))) |Int #asWord ( B1 ) ) +Bytes B2 )
        requires #rangeUInt(256, A) andBool A modInt (2 ^Int (8 *Int lengthBytes(B2))) ==Int 0 andBool lengthBytes(B1 +Bytes B2) <=Int 32
        [simplification, preserves-definedness]

    // 2b. |Int of +Bytes, update to be done in right
    rule [bor-update-to-right]:
      A |Int #asWord ( B1 +Bytes B2 ) =>
        #asWord ( B1 +Bytes #buf ( lengthBytes(B2), A |Int #asWord ( B2 ) ) )
        requires 0 <=Int A andBool A <Int 2 ^Int (8 *Int lengthBytes(B2)) andBool lengthBytes(B2) <=Int 32
        [simplification, preserves-definedness]

    // 3a. Update with explicit shift and symbolic slot
    rule [bor-update-with-shift]:
      ( SHIFT *Int X ) |Int Y => #asWord ( #buf( 32 -Int ( log2Int(SHIFT) /Int 8 ), X ) +Bytes #buf( log2Int(SHIFT) /Int 8, Y ) )
      requires #isByteShift(SHIFT)
       andBool 0 <=Int X andBool X <Int 2 ^Int (8 *Int (32 -Int ( log2Int(SHIFT) /Int 8 )))
       andBool 0 <=Int Y andBool Y <Int SHIFT
       [simplification, concrete(SHIFT), comm, preserves-definedness]

    // 3b. Buffer cropping
    rule [buf-asWord-crop]:
      #buf (W:Int , #asWord(B:Bytes)) => #range(B, lengthBytes(B) -Int W, W)
      requires 0 <=Int W andBool W <=Int 32 andBool W <Int lengthBytes(B)
       andBool #asWord ( #range(B, 0, lengthBytes(B) -Int W) ) ==Int 0
      [simplification, concrete(W), preserves-definedness]

    // 3c. Splitting the updated buffer into the updated value and the trailing zeros, explicit shift
    rule [buf-split-l]:
      #buf ( W, SHIFT *Int X ) => #buf( W -Int ( log2Int(SHIFT) /Int 8 ), X ) +Bytes #buf( log2Int(SHIFT) /Int 8, 0)
      requires 0 <=Int W andBool W <=Int 32 andBool #isByteShift(SHIFT)
       andBool 0 <=Int X andBool X <Int 2 ^Int (8 *Int (W -Int ( log2Int(SHIFT) /Int 8)))
       [simplification, concrete(W, SHIFT), preserves-definedness]

    // 3d. Splitting the updated buffer into the updated value and the trailing zeros, implicit shift
    rule [bor-split]:
      X |Int Y => #asWord ( #buf ( 32 -Int #getFirstOneBit(X) /Int 8, X /Int ( 2 ^Int ( 8 *Int ( #getFirstOneBit(X) /Int 8 ) ) ) ) +Bytes
                            #buf ( #getFirstOneBit(X) /Int 8, Y ) )
      requires #rangeUInt(256, X) andBool 0 <=Int #getFirstOneBit(X)
       andBool 0 <=Int Y andBool Y <Int 2 ^Int ( 8 *Int ( #getFirstOneBit(X) /Int 8 ) )
       [simplification, concrete(X), preserves-definedness]

endmodule
