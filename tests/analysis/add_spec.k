module SYMBOLICEXE-SPEC
	import ETHEREUM-SIMULATION


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
<gas> N =>N1 </gas>

<pc> 0 => 8 </pc>

<wordStack> .WordStack => .WordStack </wordStack>
<program> #asMap( PUSH ( 1 , 2 ) ; PUSH ( 1 ,2 ) ; ADD ; PUSH ( 1 , 1 ) ; MSTORE ; .OpCodes)</program>
requires N>=Int 10
ensures N-Int N1==Int 10


endmodule



