requires "edsl.md"

module EVM-DATA-MAP-SYMBOLIC [symbolic]
    imports K-REFLECTION
    imports EDSL

    rule ( WS1 ++ WS2 ) ++ WS3 => WS1 ++ ( WS2 ++ WS3 )
endmodule
