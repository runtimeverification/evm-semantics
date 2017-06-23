module SYMBOLICEXE-SPEC
	import ETHEREUM-SIMULATION

//To some extend, this property can not guarantee the gas enough for the execution of the program. Since if the gas is not enough, the program can also reach its final state.

rule 
<k>  

start~>flush

=>.
...
</k>

<op> . => . </op>
<memoryUsed> 0 =>N2:Int  </memoryUsed>
<localMem> .Map => M1:Map </localMem>
<gas> N:Int =>N1:Int</gas>
<pc> 0 => N3:Int </pc>
<wordStack> . => . </wordStack>
<program>PROGRAM:Map </program>

requires N>=Int 15

endmodule
