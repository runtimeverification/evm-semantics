requires "evm.k"

module ADD-SPEC
    imports EVM

    rule <k> #next [ ADD ] => . ... </k>
         <schedule> SCHEDULE </schedule>
         <wordStack> W0 : W1 : WS => chop(W0 +Int W1) : WS </wordStack>
         <pc> PCOUNT => PCOUNT +Int 1 </pc>
         <gas> G => G -Int Gverylow < SCHEDULE > </gas>
      requires G >=Int Gverylow < SCHEDULE >
       andBool notBool ( #stackUnderflow ( W0 : W1 : WS , ADD )
                  orBool #stackOverflow  ( W0 : W1 : WS , ADD )
                       )
endmodule
