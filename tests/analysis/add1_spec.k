module ADD1-SPEC
	import ETHEREUM-SIMULATION


rule 
<k>  

start~>flush
=>
.
...
</k>

<op> . => .</op>
<memoryUsed> 0 =>1  </memoryUsed>
<localMem> .Map =>(_:Map 31|->3) </localMem>
<gas> N =>N1 </gas>
<gasPrice> GPRICE:Int </gasPrice>
<gasLimit> 0 </gasLimit> 
<pc> 0 => 19 </pc>

<wordStack> .WordStack => 0:(0: .WordStack) </wordStack>
<program> #asMap( PUSH(0,0); JUMPDEST; PUSH(0,0);PUSH(1, 0); MLOAD; PUSH(1,1); ADD; PUSH(1,0); MSTORE; MLOAD;PUSH(4, 3); GT;JUMP; .OpCodes)</program>
requires N>=Int 68
ensures N-Int N1==Int 68


endmodule