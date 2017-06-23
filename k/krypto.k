module KRYPTO
     imports STRING-SYNTAX

     syntax String ::= Keccak256(String) [function, hook(KRYPTO.keccak256)]

endmodule
