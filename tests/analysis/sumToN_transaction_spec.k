module SUM-ITERATIVE-SPEC
    imports EVM

    rule
        <k> transaction:
            -   to: 2
            -   from: 2
            -   data: X
            -   value: 5000
            -   gasPrice: 1
            -   gasLimit: 5000
          => .
        </k>
        <pc> _ => 50 </pc>
        <localMem> _ => 0 |-> 0 1 |-> ((X *Int (X +Int 1)) /Int 2) </localMem>
        <accounts> ACCTS:Bag </accounts>
        requires X >=Int 0

endmodule
