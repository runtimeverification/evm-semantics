Foundry Specifications
======================

### Overview

Foundry's testing framework provides a series of cheatcodes so that developers can specify what situation they want to test.
This file describes the KEVM specification of the Foundry testing framework, which includes the definition of said cheatcodes and what does it mean for a test to pass.

```k
requires "edsl.md"
module FOUNDRY
    imports EDSL
    imports FOUNDRY-SUCCESS
    imports FOUNDRY-CHEAT-CODES
endmodule
```
Foundry Success Predicate
-------------------------
```k
module FOUNDRY-SUCCESS
    imports EVM
    syntax Bool ::= "foundry_success" "(" ")" [function]
 // --------------------------------------------
    rule foundry_success() => false
endmodule
```
Foundry Cheat Codes
-------------------
```k
module FOUNDRY-CHEAT-CODES
    imports EDSL
endmodule
```

