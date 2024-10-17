requires "word.md"

module SLOT-UPDATES [symbolic]
    imports EVM-TYPES
    imports BUF
    imports WORD

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
        [simplification(40), comm, preserves-definedness]

    // 2b. |Int of +Bytes, update to be done in right
    rule [bor-update-to-right]:
      A |Int #asWord ( B1 +Bytes B2 ) =>
        #asWord ( B1 +Bytes #buf ( lengthBytes(B2), A |Int #asWord ( B2 ) ) )
        requires 0 <=Int A andBool A <Int 2 ^Int (8 *Int lengthBytes(B2)) andBool lengthBytes(B2) <=Int 32
        [simplification(40), comm, preserves-definedness]

    // 3a. Update with explicit shift and symbolic slot
    rule [bor-update-with-shift]:
      ( SHIFT *Int X ) |Int Y => #asWord ( #buf( 32 -Int ( log2Int(SHIFT) /Int 8 ), X ) +Bytes #buf( log2Int(SHIFT) /Int 8, Y ) )
      requires #isByteShift(SHIFT)
       andBool 0 <=Int X andBool X <Int 2 ^Int (8 *Int (32 -Int ( log2Int(SHIFT) /Int 8 )))
       andBool 0 <=Int Y andBool Y <Int SHIFT
       [simplification(42), concrete(SHIFT), comm, preserves-definedness]

    // 3b. Update with implicit shift and symbolic slot
    rule [bor-update-without-shift]:
      X |Int Y => #asWord ( #buf ( 32 -Int #getFirstOneBit(X) /Int 8, X /Int ( 2 ^Int ( 8 *Int ( #getFirstOneBit(X) /Int 8 ) ) ) ) +Bytes
                            #buf ( #getFirstOneBit(X) /Int 8, Y ) )
      requires #rangeUInt(256, X) andBool 0 <=Int #getFirstOneBit(X)
       andBool 0 <=Int Y andBool Y <Int 2 ^Int ( 8 *Int ( #getFirstOneBit(X) /Int 8 ) )
       [simplification(42), concrete(X), preserves-definedness]

    // 4. Buffer cropping
    rule [buf-asWord-crop]:
      #buf (W:Int , #asWord(B:Bytes)) => #range(B, lengthBytes(B) -Int W, W)
      requires 0 <=Int W andBool W <=Int 32 andBool W <Int lengthBytes(B)
       andBool #asWord ( #range(B, 0, lengthBytes(B) -Int W) ) ==Int 0
      [simplification, concrete(W), preserves-definedness]

    // 5. Splitting the updated buffer into the updated value and the trailing zeros
    rule [buf-split-on-shift]:
      #buf ( W, SHIFT *Int X ) => #buf( W -Int ( log2Int(SHIFT) /Int 8 ), X ) +Bytes #buf( log2Int(SHIFT) /Int 8, 0)
      requires 0 <=Int W andBool W <=Int 32 andBool #isByteShift(SHIFT)
       andBool 0 <=Int X andBool X <Int 2 ^Int (8 *Int (W -Int ( log2Int(SHIFT) /Int 8)))
       [simplification, concrete(W, SHIFT), preserves-definedness]

endmodule
