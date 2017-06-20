module SUM-ITERATIVE-SPEC
    imports EVM

    rule
        <k> transaction:
            -   to: 2
            -   from: 2
            -   data: 10
            -   value: 5000
            -   gasPrice: 1
            -   gasLimit: 5000
          => .
        </k>
        <pc> _ => 50 </pc>
        <localMem> _ => 0 |-> 0 1 |-> 55 </localMem>
        <accounts> ACCTS:Bag </accounts>

endmodule
