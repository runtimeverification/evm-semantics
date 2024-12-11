requires "edsl.md"
requires "lemmas/lemmas.k"

module VERIFICATION
    imports EDSL
    imports LEMMAS

    syntax StepSort ::= Map | Bytes | Int | Bool
 // --------------------------------------------

    syntax KItem ::= runLemma ( StepSort ) [symbol(runLemma)]
                   | doneLemma( StepSort )
 // --------------------------------------
    rule runLemma( T ) => doneLemma( T )

endmodule

module SLOT-UPDATES-SPEC
    imports VERIFICATION

    //
    //  Auxiliary functions
    //

    claim [gfob-min]: <k> runLemma( #getFirstOneBit(0         ) ) => doneLemma( -1 ) ... </k>
    claim [gfob-max]: <k> runLemma( #getFirstOneBit(maxUInt256) ) => doneLemma(  0 ) ... </k>

    claim [gfzb-min]: <k> runLemma( #getFirstZeroBit(0         ) ) => doneLemma(  0 ) ... </k>
    claim [gfzb-max]: <k> runLemma( #getFirstZeroBit(maxUInt256) ) => doneLemma( -1 ) ... </k>

    claim [gmsb-01]: <k> runLemma ( #getMaskShiftBits(0) ) => doneLemma ( 0 ) ... </k>
    claim [gmsb-02]: <k> runLemma ( #getMaskShiftBits(2 ^Int 164 -Int 1) ) => doneLemma ( 164 ) ... </k>
    claim [gmsb-03]: <k> runLemma ( #getMaskShiftBits(pow256) ) => doneLemma ( -1 ) ... </k>
    claim [gmsb-04]: <k> runLemma ( #getMaskShiftBits(115341543235797707419527244145998463631733976271937281205136574426583511597055) ) => doneLemma ( 240 ) ... </k>
    claim [gmsb-05]: <k> runLemma ( #getMaskShiftBits(115790322390251417039241401711187164934754157181743689629425282016341011726335) ) => doneLemma ( 80  ) ... </k>
    claim [gmsb-06]: <k> runLemma ( #getMaskShiftBits(115792089237316195423570985008687907853269984665640254554447762944319381569535) ) => doneLemma ( 48  ) ... </k>

    claim [gmsby-01]: <k> runLemma ( #getMaskShiftBytes(0) ) => doneLemma ( 0 ) ... </k>
    claim [gmsby-02]: <k> runLemma ( #getMaskShiftBytes(2 ^Int 164 -Int 1) ) => doneLemma ( -1 ) ... </k>
    claim [gmsby-03]: <k> runLemma ( #getMaskShiftBytes(pow256) ) => doneLemma ( -1 ) ... </k>
    claim [gmsby-04]: <k> runLemma ( #getMaskShiftBytes(115341543235797707419527244145998463631733976271937281205136574426583511597055) ) => doneLemma ( 30 ) ... </k>
    claim [gmsby-05]: <k> runLemma ( #getMaskShiftBytes(115790322390251417039241401711187164934754157181743689629425282016341011726335) ) => doneLemma ( 10 ) ... </k>
    claim [gmsby-06]: <k> runLemma ( #getMaskShiftBytes(115792089237316195423570985008687907853269984665640254554447762944319381569535) ) => doneLemma ( 6  ) ... </k>

    claim [gmwb-01]: <k> runLemma ( #getMaskWidthBits(0) ) => doneLemma ( 256 ) ... </k>
    claim [gmwb-02]: <k> runLemma ( #getMaskWidthBits(2 ^Int 164 -Int 1) ) => doneLemma ( 92 ) ... </k>
    claim [gmwb-03]: <k> runLemma ( #getMaskWidthBits(pow256) ) => doneLemma ( -1 ) ... </k>
    claim [gmwb-04]: <k> runLemma ( #getMaskWidthBits(115341543235797707419527244145998463631733976271937281205136574426583511597055) ) => doneLemma ( 8   ) ... </k>
    claim [gmwb-05]: <k> runLemma ( #getMaskWidthBits(115790322390251417039241401711187164934754157181743689629425282016341011726335) ) => doneLemma ( 160 ) ... </k>
    claim [gmwb-06]: <k> runLemma ( #getMaskWidthBits(115792089237316195423570985008687907853269984665640254554447762944319381569535) ) => doneLemma ( 40  ) ... </k>

    claim [gmwby-01]: <k> runLemma ( #getMaskWidthBytes(0) ) => doneLemma ( 32 ) ... </k>
    claim [gmwby-02]: <k> runLemma ( #getMaskWidthBytes(2 ^Int 164 -Int 1) ) => doneLemma ( -1 ) ... </k>
    claim [gmwby-03]: <k> runLemma ( #getMaskWidthBytes(pow256) ) => doneLemma ( -1 ) ... </k>
    claim [gmwby-04]: <k> runLemma ( #getMaskWidthBytes(115341543235797707419527244145998463631733976271937281205136574426583511597055) ) => doneLemma ( 1  ) ... </k>
    claim [gmwby-05]: <k> runLemma ( #getMaskWidthBytes(115790322390251417039241401711187164934754157181743689629425282016341011726335) ) => doneLemma ( 20 ) ... </k>
    claim [gmwby-06]: <k> runLemma ( #getMaskWidthBytes(115792089237316195423570985008687907853269984665640254554447762944319381569535) ) => doneLemma ( 5  ) ... </k>

    claim [is-mask-01]: <k> runLemma( #isMask(maxUInt8                                                                      ) ) => doneLemma( true  ) ... </k>
    claim [is-mask-02]: <k> runLemma( #isMask(maxUInt40                                                                     ) ) => doneLemma( true  ) ... </k>
    claim [is-mask-03]: <k> runLemma( #isMask(115341543235797707419527244145998463631733976271937281205136574426583511597055) ) => doneLemma( true  ) ... </k>
    claim [is-mask-04]: <k> runLemma( #isMask(115790322390251417039241401711187164934754157181743689629425282016341011726335) ) => doneLemma( true  ) ... </k>
    claim [is-mask-05]: <k> runLemma( #isMask(115792089237316195423570985008687907853269984665640254554447762944319381569535) ) => doneLemma( true  ) ... </k>
    claim [is-mask-06]: <k> runLemma( #isMask(115792089237316195423570985008687907813269984665640254554447762944319381569535) ) => doneLemma( false ) ... </k>
    claim [is-mask-07]: <k> runLemma( #isMask(115792089237316195423570985008687907853269984635640254554447762944319381569535) ) => doneLemma( false ) ... </k>
    claim [is-mask-08]: <k> runLemma( #isMask(115792089237316195473570985008687907853269984665640254554447762944319381569535) ) => doneLemma( false ) ... </k>

    claim [byte-shift-01]: <k> runLemma( #isByteShift(0          ) ) => doneLemma( false ) ... </k>
    claim [byte-shift-02]: <k> runLemma( #isByteShift(maxUInt40  ) ) => doneLemma( false ) ... </k>
    claim [byte-shift-03]: <k> runLemma( #isByteShift(maxUInt160 ) ) => doneLemma( false ) ... </k>
    claim [byte-shift-04]: <k> runLemma( #isByteShift(maxUInt240 ) ) => doneLemma( false ) ... </k>
    claim [byte-shift-05]: <k> runLemma( #isByteShift(pow40      ) ) => doneLemma( true  ) ... </k>
    claim [byte-shift-06]: <k> runLemma( #isByteShift(pow160     ) ) => doneLemma( true  ) ... </k>
    claim [byte-shift-07]: <k> runLemma( #isByteShift(2 ^Int 164 ) ) => doneLemma( false ) ... </k>
    claim [byte-shift-08]: <k> runLemma( #isByteShift(pow240     ) ) => doneLemma( true  ) ... </k>
    claim [byte-shift-09]: <k> runLemma( #isByteShift(pow256     ) ) => doneLemma( false ) ... </k>

    //
    //  From real-world examples
    //

    claim [slot-update-01]:
      <k> runLemma(
        ( maxUInt8 &Int ( ( TIMESTAMP_CELL:Int *Int pow48 ) |Int ( 115792089237316195423570985008687907853269984665640254554447762944319381569535 &Int ( ( TIMESTAMP_CELL:Int *Int 256 ) |Int ( 115792089237316195423570985008687907853269984665640564039457583726438152929535 &Int ( 1 |Int #asWord ( b"\x00E\xc9,,\xd0\xdf{-p^\xf1,\xffw\xcb\x0b\xc5W\xed\"" +Bytes #buf ( 5 , _WORD4:Int ) +Bytes #buf ( 5 , _WORD3:Int ) +Bytes b"\x00" ) ) ) ) ) ) )
      ) => doneLemma(
        1
      ) ... </k>
      requires 0 <=Int TIMESTAMP_CELL andBool TIMESTAMP_CELL <Int 2 ^Int 40

    claim [slot-update-02]:
      <k> runLemma (
            ( ( maxUInt40 &Int ( ( 115341543235797707419527244145998463631733976271937281205136574426583511597055 &Int #asWord ( #buf ( 2 , WORD7:Int ) +Bytes b"\xa4\xadOh\xd0\xb9\x1c\xfd\x19h|\x88\x1eP\xf3\xa0\x02B\x82\x8c" +Bytes #buf ( 5 , TIMESTAMP_CELL:Int ) +Bytes #buf ( 5 , WORD5:Int ) ) ) /Int pow40 ) ) )
          ) => doneLemma (
            TIMESTAMP_CELL
          ) ... </k>
          requires 0 <=Int TIMESTAMP_CELL andBool TIMESTAMP_CELL <Int 2 ^Int 35

    claim [slot-update-03]:
      <k> runLemma (
            ( maxUInt40 &Int ( ( TIMESTAMP_CELL:Int |Int ( 115792089237316195423570985008687907853269984665640564039457584006813618012160 &Int #asWord ( #buf ( 1 , WORD7:Int ) +Bytes b"\xa4\xadOh\xd0\xb9\x1c\xfd\x19h|\x88\x1eP\xf3\xa0\x02B\x82\x8c" +Bytes #buf ( 5 , WORD6:Int ) +Bytes #buf ( 5 , WORD5:Int ) ) ) ) /Int pow40 ) )
          ) => doneLemma (
            #asWord ( #buf ( 5 , WORD6:Int ) )
          ) ... </k>
          requires 0 <=Int TIMESTAMP_CELL andBool TIMESTAMP_CELL <Int 2 ^Int 35

    claim [slot-update-04]:
      <k> runLemma (
            #asWord ( #range ( #buf ( 10 , ( ( ( TIMESTAMP_CELL:Int *Int pow48 ) /Int 256 ) |Int TIMESTAMP_CELL:Int ) ) , 5 , 5 ) ) <=Int TIMESTAMP_CELL:Int
          ) => doneLemma (
            true
          ) ... </k>
          requires 0 <=Int TIMESTAMP_CELL andBool TIMESTAMP_CELL <Int 2 ^Int 35

    claim [slot-update-05]:
      <k> runLemma (
            #asWord ( #range ( #buf ( 6 , TIMESTAMP_CELL:Int *Int 256 ) , 5 , 1 ) )
          ) => doneLemma (
            0
          ) ... </k>
          requires 0 <=Int TIMESTAMP_CELL andBool TIMESTAMP_CELL <Int 2 ^Int 35

    claim [slot-update-06]:
      <k> runLemma (
            #asWord ( #range ( #buf ( 26 , 960911443338137442927181681227604902095826437272264907948032 |Int WORD4:Int ) , 21 , 5 ) ) <=Int TIMESTAMP_CELL:Int
          ) => doneLemma (
            WORD4 <=Int TIMESTAMP_CELL
          ) ... </k>
          requires 0 <=Int WORD4 andBool WORD4 <Int 2 ^Int 40

    claim [slot-update-07]:
      <k> runLemma (
            ( 481644099385675654177479669474857658256926169505224677670350078624137216 |Int ( 115790322390251417039241401711187164934754157181743689629425282016341011726335 &Int #asWord ( #buf ( 2 , WORD7:Int ) +Bytes b"\xa4\xadOh\xd0\xb9\x1c\xfd\x19h|\x88\x1eP\xf3\xa0\x02B\x82\x8c" +Bytes #buf ( 5 , WORD6:Int ) +Bytes #buf ( 5 , WORD5:Int ) ) ) )
          ) => doneLemma (
            #asWord ( #buf ( 2 , WORD7:Int ) +Bytes b"E\xc9,,\xd0\xdf{-p^\xf1,\xffw\xcb\x0b\xc5W\xed\"" +Bytes #buf ( 5 , WORD6:Int ) +Bytes #buf ( 5 , WORD5:Int ) )
          ) ... </k>
          requires 0 <=Int WORD5 andBool WORD5 <Int 2 ^Int 35
           andBool 0 <=Int WORD6 andBool WORD6 <Int 2 ^Int 35
           andBool 0 <=Int WORD7 andBool WORD7 <Int 256

    claim [slot-update-08]:
      <k> runLemma ( X &Int #asWord ( BA ) ==Int Y:Int ) => doneLemma ( true ) ... </k>
      requires 0 <=Int X andBool X <Int 2 ^Int (8 *Int lengthBytes(BA))
      andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
      andBool log2Int (X +Int 1) modInt 8 ==Int 0
      andBool log2Int(X +Int 1) /Int 8 <=Int lengthBytes(BA) andBool lengthBytes(BA) <=Int 32
      andBool #asWord ( #range(BA, lengthBytes(BA) -Int (log2Int(X +Int 1) /Int 8), log2Int(X +Int 1) /Int 8) ) ==Int Y
      andBool X ==Int 2 ^Int ( 8 *Int 5 ) -Int 1 // 5 can be replaced by any number between 0 and 32

    claim [slot-update-09]:
      <k> runLemma ( X &Int #asWord ( BA ) ==Int Y:Int ) => doneLemma ( false ) ... </k>
      requires 0 <=Int X andBool X <Int 2 ^Int (8 *Int lengthBytes(BA))
      andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
      andBool log2Int (X +Int 1) modInt 8 ==Int 0
      andBool log2Int(X +Int 1) /Int 8 <=Int lengthBytes(BA) andBool lengthBytes(BA) <=Int 32
      andBool notBool #asWord ( #range(BA, lengthBytes(BA) -Int (log2Int(X +Int 1) /Int 8), log2Int(X +Int 1) /Int 8) ) ==Int Y
      andBool X ==Int 2 ^Int ( 8 *Int 5 ) -Int 1 // 5 can be replaced by any number between 0 and 32

    claim [slot-update-10]:
      <k> runLemma ( X &Int #asWord ( BA ) <Int Y:Int ) => doneLemma ( true ) ... </k>
      requires 0 <=Int X andBool X <Int 2 ^Int (8 *Int lengthBytes(BA))
      andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
      andBool log2Int (X +Int 1) modInt 8 ==Int 0
      andBool log2Int(X +Int 1) /Int 8 <=Int lengthBytes(BA) andBool lengthBytes(BA) <=Int 32
      andBool #asWord ( #range(BA, lengthBytes(BA) -Int (log2Int(X +Int 1) /Int 8), log2Int(X +Int 1) /Int 8) ) <Int Y
      andBool X ==Int 2 ^Int ( 8 *Int 5 ) -Int 1 // 5 can be replaced by any number between 0 and 32

    claim [slot-update-11]:
      <k> runLemma ( X &Int #asWord ( BA ) <Int Y:Int ) => doneLemma ( false ) ... </k>
      requires 0 <=Int X andBool X <Int 2 ^Int (8 *Int lengthBytes(BA))
      andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
      andBool log2Int (X +Int 1) modInt 8 ==Int 0
      andBool log2Int(X +Int 1) /Int 8 <=Int lengthBytes(BA) andBool lengthBytes(BA) <=Int 32
      andBool notBool #asWord ( #range(BA, lengthBytes(BA) -Int (log2Int(X +Int 1) /Int 8), log2Int(X +Int 1) /Int 8) ) <Int Y
      andBool X ==Int 2 ^Int ( 8 *Int 5 ) -Int 1 // 5 can be replaced by any number between 0 and 32

    claim [slot-update-12]:
      <k> runLemma ( X &Int #asWord ( BA ) <=Int Y:Int ) => doneLemma ( true ) ... </k>
      requires 0 <=Int X andBool X <Int 2 ^Int (8 *Int lengthBytes(BA))
      andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
      andBool log2Int (X +Int 1) modInt 8 ==Int 0
      andBool log2Int(X +Int 1) /Int 8 <=Int lengthBytes(BA) andBool lengthBytes(BA) <=Int 32
      andBool #asWord ( #range(BA, lengthBytes(BA) -Int (log2Int(X +Int 1) /Int 8), log2Int(X +Int 1) /Int 8) ) <=Int Y
      andBool X ==Int 2 ^Int ( 8 *Int 5 ) -Int 1 // 5 can be replaced by any number between 0 and 32

    claim [slot-update-13]:
      <k> runLemma ( X &Int #asWord ( BA ) <=Int Y:Int ) => doneLemma ( false ) ... </k>
      requires 0 <=Int X andBool X <Int 2 ^Int (8 *Int lengthBytes(BA))
      andBool X +Int 1 ==Int 2 ^Int log2Int(X +Int 1)
      andBool log2Int (X +Int 1) modInt 8 ==Int 0
      andBool log2Int(X +Int 1) /Int 8 <=Int lengthBytes(BA) andBool lengthBytes(BA) <=Int 32
      andBool notBool #asWord ( #range(BA, lengthBytes(BA) -Int (log2Int(X +Int 1) /Int 8), log2Int(X +Int 1) /Int 8) ) <=Int Y
      andBool X ==Int 2 ^Int ( 8 *Int 5 ) -Int 1 // 5 can be replaced by any number between 0 and 32

endmodule
