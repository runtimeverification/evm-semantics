The Sum To N Specification file
===============================

Here we provide a specification file containing two reachability rules:
(1) Main rule stating the functional correctness of the program, including the gas that it needs; and
(2) The helper circularity rule stating the functional correctness of its loop and the gas it needs.
Note that the program behaves incorrectly/unexpectedly if arithmetic overflow occurs during its execution.
One challenge in verifying this program is to identify the conditions under which overflow does not occur.

```{.k .sum-to-n}
module SUM-SPEC
    imports ETHEREUM-SIMULATION
```

Primary Claim
-------------

The first part of the claim is largely static (or abstracted away, like `<previousGas>`).

```{.k .sum-to-n}
    rule <k> #execute ... </k>
         <mode> NORMAL </mode>
         <schedule> DEFAULT </schedule>
         <callStack> .List </callStack>
         <memoryUsed> 0   </memoryUsed>
         <localMem> .Map </localMem>
         <previousGas> _ => _ </previousGas>
         <program> sumTo(N) </program>
```

Here is the meat of the proof-claims:

-   We start at program counter 0 and end at 53.
-   The `<wordStack>` starts at anything sufficiently small and ends with the correct sum in the second position.
-   The gas consumed is no more than `(52 * N) + 27` to execute this program.
-   `N` is sufficiently low that overflow will not occur in execution.

```{.k .sum-to-n}
         <pc>        0  => 53                                </pc>
         <wordStack> WS => 0 : N *Int (N +Int 1) /Int 2 : WS </wordStack>
         <gas>       G  => G -Int (52 *Int N +Int 27)        </gas>

      requires N >=Int 0
       andBool N <=Int 340282366920938463463374607431768211455  // largest integer for which the program does not overflow, a test point to the program for checking overflow of the sum program
       andBool #sizeWordStack(WS) <Int 1021
       andBool G >=Int 52 *Int N +Int 27
```

Circularity
-----------

The circularity is in the same static environment as the overall proof-goal.

```{.k .sum-to-n}
    rule <k> #execute ... </k>
         <mode> NORMAL </mode>
         <schedule> DEFAULT </schedule>
         <callStack> .List </callStack>
         <memoryUsed> 0   </memoryUsed>
         <localMem> .Map </localMem>
         <previousGas> _ => _ </previousGas>
         <program> sumTo(N) </program>
```

Here, we are providing the behaviour of the rest of the program at any point it reaches the head of the loop:

-   We start at program counter 35 and end at 53.
-   The `<wordStack>` starts with the current counter `I` and the partial sum `S` and ends with the correct sum in the second position.
-   The gas consumed from the beginning of the loop to the end is no more than `(52 * I) + 21`.
-   `S` and `I` are sufficiently low that overflow will not occur during execution.

```{.k .sum-to-n}
         <pc>        35         => 53                                       </pc>
         <wordStack> I : S : WS => 0 : S +Int I *Int (I +Int 1) /Int 2 : WS </wordStack>
         <gas>       G          => G -Int (52 *Int I +Int 21)               </gas>

      requires I >=Int 0
       andBool S >=Int 0
       andBool S +Int I *Int (I +Int 1) /Int 2 <Int pow256
       andBool #sizeWordStack(WS) <Int 1021
       andBool G >=Int 52 *Int I +Int 21
endmodule
```
