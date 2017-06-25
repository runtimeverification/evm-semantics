module SYMBOLICEXE-SPEC
	import ETHEREUM-SIMULATION

//To some extend, this property can not guarantee the gas enough for the execution of the program. Since if the gas is not enough, the program can also reach its final state.

rule 
<k>  

start~>flush
=>
.
...
</k>

<op> . => .</op>
<memoryUsed> 0 =>2  </memoryUsed>
<localMem> .Map =>(_:Map 32|->4) </localMem>
<gas> 10 =>0 </gas>
<gasPrice> GPRICE:Int </gasPrice>
<gasLimit> 0 </gasLimit> 
<pc> 0 => 8 </pc>

<wordStack> .WordStack => .WordStack </wordStack>
<program> #asMap( PUSH ( 1 , 2 ) ; PUSH ( 1 ,2 ) ; ADD ; PUSH ( 1 , 1 ) ; MSTORE ; .OpCodes)</program>
//requires N>=Int 10
//ensures N-Int N1==Int 10


endmodule

