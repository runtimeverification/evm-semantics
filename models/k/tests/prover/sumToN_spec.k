requires "../../evm-semantics.k"

module SUM-ITERATIVE-SPEC
    imports EVM

    rule
        <pc> 12 </pc> 
        <localMem> 0 |-> V0:Int 1 |-> 0 </localMem> 
        
        => 
        
        <pc> 50 </pc>
        <localMem> 0 |-> 0 1 |-> ((V0 *Int (V0 +Int 1)) /Int 2)


    rule
        <pc> 12 </pc> 
        <localMem> 0 |-> X:Int 1 |-> Y:Int </localMem> 
        
        => 
        
        <pc> 50 </pc>
        <localMem> 0 |-> 0 1 |-> Y +Int ((X *Int (X +Int 1)) /Int 2) </localMem>
endmodule


