requires "evm.k"

module ADD-OVERFLOW-SPEC
    imports EVM

    rule <k> #next [ ADD ] => . ... </k>
         <schedule> SCHEDULE </schedule>
         <wordStack> W0 : W1 : WS => chop(W0 +Int W1) : WS </wordStack>
         <wordStackSize> WSSIZE => WSSIZE -Int 1 </wordStackSize>
         <pc> PCOUNT => PCOUNT +Int 1 </pc>
         <gas> G => G -Int Gverylow < SCHEDULE > </gas>
      requires G >=Int Gverylow < SCHEDULE >
       andBool notBool ( #stackUnderflow ( WSSIZE , ADD )
                       )
endmodule
