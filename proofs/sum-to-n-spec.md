The Sum To N Specification file
===============================

Here we provide a specification file containing two reachability rules - the main
proof rule and the circularity rule.

```{.k}
module ADD1-SPEC
    import ETHEREUM-SIMULATION

rule
<k>
.
</k>
<mode> NORMAL </mode>
<schedule> DEFAULT </schedule>
<op>  #execute => #execute</op>
<memoryUsed> 0   </memoryUsed>
 <callStack> .List => .List </callStack>
<localMem> .Map </localMem>
<gas> N =>N1 </gas>
<previousGas> 0 => N1+Int 2 </previousGas>
<pc> 0 => 23 </pc>
 <id> ACCT </id>
  <network>
<activeAccounts>   SetItem (ACCT)   </activeAccounts>

 <accounts>
 ...
<account>
<acctID> ACCT </acctID>
<storage> .Map</storage>
...
</account>
...
</accounts>
<messages> .Bag </messages>
</network>
<wordStack> .WordStack => (I *Int (I +Int 1)/Int 2) : .WordStack </wordStack>
<program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ;
SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; POP ; .OpCodes
)</program>
requires N>=Int (52*Int I) +Int 29 andBool I>=Int 1  andBool I<Int 2^Int 256
ensures N-Int N1==Int (52*Int I )+Int 29


//loop invariant
rule
<k> . </k>
<mode> NORMAL </mode>
<schedule> DEFAULT </schedule>
<op> #execute=> #execute</op>
<memoryUsed> 0  </memoryUsed>
<callStack> .List => .List </callStack>
<localMem>.Map</localMem>
<gas> N =>N1 </gas>
<previousGas> N+Int 8 => N1+Int 2 </previousGas>
<pc> 4=>23</pc>
 <id> ACCT </id>
  <network>
<activeAccounts>   SetItem (ACCT)   </activeAccounts>
 <accounts>
<account>
<acctID> ACCT </acctID>
<storage> .Map</storage>
...
</account>
</accounts>
<messages> .Bag </messages>
</network>

<program> #asMapOpCodes( PUSH(1, 0) ; PUSH(1, I)
; JUMPDEST ; DUP(1) ; ISZERO ; PUSH(1, 21) ; JUMPI ; DUP(1) ; SWAP(2) ; ADD ; SWAP(1) ; PUSH(1, 1) ;
SWAP(1) ; SUB ; PUSH(1, 4) ; JUMP ; JUMPDEST ; POP ;
 .OpCodes)</program>
<wordStack> I1:Int : I2:Int : .WordStack =>(I2 +Int (I1 *Int (I1 -Int 1)/Int 2)) : .WordStack </wordStack>

requires N>=Int (52*Int I1) +Int 23 andBool I1>=Int 0  andBool I1<=Int I andBool I2>=Int 0 andBool I1<Int 2^Int 256 andBool I2<Int 2^Int 256
ensures N-Int N1==Int (52*Int I1 )+Int 23

endmodule
```
