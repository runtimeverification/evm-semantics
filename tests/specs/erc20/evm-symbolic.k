requires "edsl.md"

module EVM-SYMBOLIC     [symbolic]
    imports EVM
    imports EDSL

  // ########################
  // Symbolic Gas
  // ########################

    /* startGas - gas available at the beginning of execution
       nonMemory - gas consumed on non-memory operations
       memory - gas consumed on memory operation

       Concrete semantics:

       rule #gas ( StartGas , NonMemory , Memory ) => StartGas -Int NonMemory -Int Memory
    */

    syntax Int ::= #gas ( Int , Int , Int )  [function]  // startGas, nonMemory, memory
 // -----------------------------------------------------------------------------------

endmodule
