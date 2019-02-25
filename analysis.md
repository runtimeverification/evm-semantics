Analysis Tools
==============

Here, we define analysis tools specific to EVM.
These tools are defined as extensions of the semantics, utilizing the underlying machinery to do execution.
One benefit of K is that we do not have to re-specify properties about the operational behavior in our analysis tools; instead we can take the operational behavior directly.

```{.k .standalone}
requires "evm.k"

module EVM-ANALYSIS
    imports EVM
```

Gas Analysis
------------

Gas analysis tools will help in determining how much gas to call a contract with given a specific input.
This can be used to ensure that computation will finish without throwing an exception and rolling back state.
Here we provide a simplistic gas analysis tool (which just returns an approximation of the gas used for each basic block).
This tool should be extended to take advantage of the symbolic execution engine so that we can provide proper bounds on the gas used.

-   The mode `GASANALYZE` performs gas analysis of the program instead of executing normally.

```{.k .standalone}
    syntax Mode ::= "GASANALYZE" [klabel(GASANALYZE), symbol]
```

We'll need to make summaries of the state which collect information about how much gas has been used.

-   `#beginSummary` appends a new (unfinished) summary entry in the `analysis` cell under the key `"gasAnalyze"`.
-   `#endSummary` looks for an unfinished summary entry by the key `"gasAnalyze"` and performs the substraction necessary to state how much gas has been used since the corresponding `#beginSummary`.

```{.k .standalone}
    syntax Summary ::= "{" Int "|" Int "|" Int "}"
                     | "{" Int "==>" Int "|" Int "|" Int "}"
 // --------------------------------------------------------

    syntax InternalOp ::= "#beginSummary"
 // -------------------------------------
    rule <k> #beginSummary => . ... </k> <pc> PCOUNT </pc> <gas> GAVAIL </gas> <memoryUsed> MEMUSED </memoryUsed>
         <analysis> ... "blocks" |-> ((.List => ListItem({ PCOUNT | GAVAIL | MEMUSED })) REST) ... </analysis>

    syntax KItem ::= "#endSummary"
 // ------------------------------
    rule <statusCode> EVMC_SUCCESS </statusCode> <k> (#halt => .) ~> #endSummary ... </k>
    rule <k> #endSummary => . ... </k> <pc> PCOUNT </pc> <gas> GAVAIL </gas> <memoryUsed> MEMUSED </memoryUsed>
         <analysis> ... "blocks" |-> (ListItem({ PCOUNT1 | GAVAIL1 | MEMUSED1 } => { PCOUNT1 ==> PCOUNT | GAVAIL1 -Int GAVAIL | MEMUSED -Int MEMUSED1 }) REST) ... </analysis>
```

-   In `GASANALYZE` mode, summaries of the state are taken at each `#gasBreaks` opcode, otherwise execution is as in `NORMAL`.

```{.k .standalone}
    rule <mode> GASANALYZE </mode>
         <k> #next => #setMode NORMAL ~> #execTo #gasBreaks ~> #setMode GASANALYZE ... </k>
         <pc> PCOUNT </pc>
         <program> ... PCOUNT |-> OP ... </program>
      requires notBool (OP in #gasBreaks)

    rule <mode> GASANALYZE </mode>
         <k> #next => #endSummary ~> #setPC (PCOUNT +Int 1) ~> #setGas 1000000000 ~> #beginSummary ~> #next ... </k>
         <pc> PCOUNT </pc>
         <program> ... PCOUNT |-> OP ... </program>
      requires OP in #gasBreaks

    syntax Set ::= "#gasBreaks" [function]
 // --------------------------------------
    rule #gasBreaks => (SetItem(JUMP) SetItem(JUMPI) SetItem(JUMPDEST))

    syntax InternalOp ::= "#setPC"  Int
                        | "#setGas" Int
 // -----------------------------------
    rule <k> #setPC PCOUNT  => . ... </k> <pc> _ => PCOUNT </pc>
    rule <k> #setGas GAVAIL => . ... </k> <gas> _ => GAVAIL </gas>
```

-   `#gasAnalyze` analyzes the gas of a chunk of code by setting up the analysis state appropriately and then setting the mode to `GASANALYZE`.

```{.k .standalone}
    syntax KItem ::= "#gasAnalyze"
 // ------------------------------
    rule <k> #gasAnalyze => #setGas 1000000000 ~> #beginSummary ~> #setMode GASANALYZE ~> #execute ~> #endSummary ... </k>
         <pc> _ => 0 </pc>
         <gas> _ => 1000000000 </gas>
         <analysis> _ => ("blocks" |-> .List) </analysis>
```

Test Coverage Analysis
------------

This tool will be used to measure the code coverage of a test. It records the program counter of each executed opcode and saves the total set of the program's opcodes.

-    At the beginning of the test's execution, two keys are added to the `analysis` map, one which points to the set which will contain all executed opcodes and one which points to the whole program.

```{.k .standalone}
    syntax Mode ::= "COVERAGE" [klabel(COVERAGE), symbol]
// ------------------------------------------------------
    rule <mode> COVERAGE </mode>
         <k> #next ... </k>
         <analysis> ANALYSIS => ANALYSIS ["coverage" <- .Set]["currentProgram" <- PROGRAM] </analysis>
         <program> PROGRAM </program>
      requires notBool("coverage" in_keys(ANALYSIS)) andBool notBool("currentProgram" in_keys(ANALYSIS))
```

-    `COVERAGE` mode is built on top of the `NORMAL` execution mode. Before each opcode, the program count is stored within the `analysis` cell and then execution resumes normally. After the opcode is executed, the mode is switched back to `COVERAGE` in order to store the next opcode's program counter.

```{.k .standalone}
    rule <mode> COVERAGE </mode>
         <k> #next 
          => #setMode NORMAL
          ~> #next
          ~> #setMode COVERAGE
          ...
         </k> 
         <pc> PCOUNT </pc>
         <analysis> ... "coverage" |-> (PCS:Set (.Set => SetItem(PCOUNT))) ... </analysis>
endmodule
```
