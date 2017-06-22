module SYMBOLICEXE-SPEC
	import ETHEREUM-SIMULATION

//To some extend, this property can not guarantee the gas enough for the execution of the program. Since if the gas is not enough, the program can also reach its final state.

rule 
<k>  

start~>flush

=>.
...
</k>
<op>. => #finalize </op>

<memoryUsed> 0 =>_  </memoryUsed>
<localMem> .Map => M1:Map </localMem>
<gas> N:Int =>_</gas>
<pc> 0 => _ </pc>
<program> PROGRAM:Map</program>

requires N>=Int 30
		
endmodule

