module SUM-ITERATIVE-SPEC
    imports EVM

    rule
        <k> JUMP1 => . </k>
        <id> 2 </id>
        <pc> 7 => 50 </pc>
        <gas> _ => _ </gas> 
        <localMem> 0 |-> (X:Int => 0) 1 |-> (0 => ((X *Int (X +Int 1)) /Int 2)) </localMem>
        <wordStack> .WordStack => .WordStack </wordStack>
        <accounts>
            ACCTS:Bag
        </accounts>
        requires X >=Int 0

    //loop invariant
    rule
        <k> JUMP1 => . </k>
        <pc> 7 => 50 </pc>
        <localMem> 0 |-> (X:Int => 0) 1 |-> (Y:Int => Y +Int ((X *Int (X +Int 1)) /Int 2)) </localMem>
        <gas> _ => _</gas> 
        <wordStack> .WordStack => .WordStack </wordStack>
        <accounts>
            ACCTS:Bag
        </accounts>
        requires X >=Int 0

endmodule
