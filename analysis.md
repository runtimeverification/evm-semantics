Analysis Tools
==============

Here, we define analysis tools specific to EVM.
These tools are defined as extensions of the semantics, utilizing the underlying machinery to do execution.
One benefit of K is that we do not have to re-specify properties about the operational behavior in our analysis tools; instead we can take the operational behavior directly.

```{.k .java .ocaml}
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

```{.k .java .ocaml}
    syntax Mode ::= "GASANALYZE"
```

We'll need to make summaries of the state which collect information about how much gas has been used.

-   `#beginSummary` appends a new (unfinished) summary entry in the `analysis` cell under the key `"gasAnalyze"`.
-   `#endSummary` looks for an unfinished summary entry by the key `"gasAnalyze"` and performs the substraction necessary to state how much gas has been used since the corresponding `#beginSummary`.

```{.k .java .ocaml}
    syntax Summary ::= "{" Int "|" Int "|" Int "}"
                     | "{" Int "==>" Int "|" Int "|" Int "}"
 // --------------------------------------------------------

    syntax InternalOp ::= "#beginSummary"
 // -------------------------------------
    rule <k> #beginSummary => . ... </k> <pc> PCOUNT </pc> <gas> GAVAIL </gas> <memoryUsed> MEMUSED </memoryUsed>
         <analysis> ... "blocks" |-> ((.List => ListItem({ PCOUNT | GAVAIL | MEMUSED })) REST) ... </analysis>

    syntax KItem ::= "#endSummary"
 // ------------------------------
    rule <k> (#end => .) ~> #endSummary ... </k>
    rule <k> #endSummary => . ... </k> <pc> PCOUNT </pc> <gas> GAVAIL </gas> <memoryUsed> MEMUSED </memoryUsed>
         <analysis> ... "blocks" |-> (ListItem({ PCOUNT1 | GAVAIL1 | MEMUSED1 } => { PCOUNT1 ==> PCOUNT | GAVAIL1 -Int GAVAIL | MEMUSED -Int MEMUSED1 }) REST) ... </analysis>
```

-   In `GASANALYZE` mode, summaries of the state are taken at each `#gasBreaks` opcode, otherwise execution is as in `NORMAL`.

```{.k .java .ocaml}
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

```{.k .java .ocaml}
    syntax KItem ::= "#gasAnalyze"
 // ------------------------------
    rule <k> #gasAnalyze => #setGas 1000000000 ~> #beginSummary ~> #setMode GASANALYZE ~> #execute ~> #endSummary ... </k>
         <pc> _ => 0 </pc>
         <gas> _ => 1000000000 </gas>
         <analysis> _ => ("blocks" |-> .List) </analysis>
endmodule
```
