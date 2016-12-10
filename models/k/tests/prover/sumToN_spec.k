module SUM-ITERATIVE-SPEC
    imports EVM

    rule
        <k> JUMP1 => .</k>
        <pc> _ => 50</pc>
        <localMem> 0 |-> (X => 0) 1 |-> (0 => ((X *Int (X +Int 1)) /Int 2)) </localMem> 
        requires X >=Int 0 
        

    rule
       
        <k> JUMP1 => . </k> 
        <pc> _ => 50 </pc> 
        <localMem> 0 |-> (X => 0) 1 |-> (Y => Y +Int ((X *Int (X +Int 1)) /Int 2)) </localMem> 
        requires X >=Int 0 

endmodule


