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

<<<<<<< HEAD
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
=======
<op> . => . </op>
<memoryUsed> 0 =>N2:Int  </memoryUsed>
<localMem> .Map => M1:Map </localMem>
<gas> N:Int =>N1:Int</gas>
<pc> 0 => N3:Int </pc>
<wordStack> . => . </wordStack>
<program>PROGRAM:Map </program>

requires N>=Int 15
>>>>>>> da10439d76d9f303afb6d4bc50866a1e596cb985

endmodule
