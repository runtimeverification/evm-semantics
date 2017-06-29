// RV-K requires this module is present, UIUC-K has it in the builtin includes.


module KRYPTO
    imports STRING-SYNTAX
    syntax String ::= Keccak256(String) [function, hook(KRYPTO.keccak256)]
endmodule

