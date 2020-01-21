requires "abstract-semantics-segmented-gas.k"
requires "edsl.k"
requires "evm-symbolic.k"

module VERIFICATION
    imports ABSTRACT-SEMANTICS-SEGMENTED-GAS
    imports EDSL
    imports EVM-SYMBOLIC

    //semantics of #buf
    rule #buf(LEN, BYTES) => #padToWidth(LEN, #asByteStack( BYTES )) [concrete]

    //Rules for #padToWidth with non-regular symbolic arguments.
    rule #padToWidth(32, #asByteStack(V)) => #buf(32, V)
      requires 0 <=Int V andBool V <Int pow256 andBool #notKLabel(V, "#asWord")

    rule chop ( W0:Int +Int W1:Int ) -Word W1:Int => chop ( W0 )
      requires #rangeUInt(256, W0) andBool #rangeUInt(256, W1)
endmodule
