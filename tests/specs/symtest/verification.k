requires "edsl.k"
requires "lemmas.k"

module VERIFICATION
    imports EVM
    imports EDSL
    imports LEMMAS

    // for [revert-invalid_function_identifier-0_4]

    rule #bufSeg(#buf(N, 0), 0, M) => #buf(M, 0) requires 0 <Int M andBool M <Int N

    // for [deposit-init-calldata]

    rule #take(X, #take(Y, WS)) => #take(X, WS)
      requires X <=Int Y

    // for addition overflow check

    rule X +Int Y <Int X => false requires X >=Int 0 andBool Y >=Int 0 // #range(0 <= (X +Int Y) < pow256)

endmodule
