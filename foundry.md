Foundry Specifications
======================

### Overview

Foundry's testing framework provides a series of cheatcodes so that developers can specify what situation they want to test.
This file describes the KEVM specification of the Foundry testing framework, which includes the definition of said cheatcodes and what does it mean for a test to pass.

```k
requires "evm.md"
module FOUNDRY
    imports FOUNDRY-SUCCESS
    imports FOUNDRY-CHEAT-CODES
endmodule
```

Foundry Success Predicate
-------------------------

```k
module FOUNDRY-ACCOUNTS
    imports EVM

        syntax Int ::= CALLER()                        [macro]
                     | "TEST_CONTRACT_ADDRESS" "(" ")" [macro]
                     | "CHEATCODE_ADDRESS" "(" ")"     [macro]
  // -----------------------------------------------------
    rule CALLER() => 137122462167341575662000267002353578582749290296 // 0x1804c8AB1F12E6bbf3894d4083f33e07309d1f38
    rule TEST_CONTRACT_ADDRESS() => 1032069922050249630382865877677304880282300743300 // 0xb4c79daB8f259C7Aee6E5b2Aa729821864227e84
    rule CHEATCODE_ADDRESS() => 645326474426547203313410069153905908525362434349 // 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D

endmodule
```


```k
module FOUNDRY-SUCCESS
    imports EVM
    imports FOUNDRY-ACCOUNTS

    syntax Bool ::= "foundry_success" "(" ")" [function, klabel(foundry_success), symbol]
 // -------------------------------------------------------------------------------------
    rule foundry_success() => false [owise]

    rule [[ foundry_test_success() => true ]]
    <account>
        <acctId> CHEATCODE_ADDRESS() </acctId>
        ...
    </account>

endmodule
```

Foundry Cheat Codes
-------------------

```k
module FOUNDRY-CHEAT-CODES
    imports EVM
endmodule
```

