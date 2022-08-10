Foundry Specifications
======================

### Overview

Foundry's testing framework provides a series of cheatcodes so that developers can specify what situation they want to test.
This file describes the KEVM specification of the Foundry testing framework, which includes the definition of said cheatcodes and what does it mean for a test to pass.

```k
requires "evm.md"
requires "hashed-locations.md"

module FOUNDRY
    imports FOUNDRY-SUCCESS
    imports FOUNDRY-CHEAT-CODES
endmodule
```

Foundry Success Predicate
-------------------------

```k
module FOUNDRY-ACCOUNTS
    imports SOLIDITY-FIELDS

    syntax Contract        ::= FoundryContract
    syntax Field           ::= FoundryField
    syntax FoundryContract ::= "Foundry"      [klabel(contract_Foundry)]
                             | "FoundryTest"  [klabel(contract_FoundryTest)]
                             | "FoundryCheat" [klabel(contract_FoundryCheat)]
    syntax FoundryField    ::= "Failed"       [klabel(slot_failed)]
 // -------------------------------------------------------------------------
    rule #address(Foundry)      => 137122462167341575662000267002353578582749290296  // 0x1804c8AB1F12E6bbf3894d4083f33e07309d1f38
    rule #address(FoundryTest)  => 1032069922050249630382865877677304880282300743300 // 0xb4c79daB8f259C7Aee6E5b2Aa729821864227e84
    rule #address(FoundryCheat) => 645326474426547203313410069153905908525362434349  // 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D
    rule #loc(FoundryCheat . Failed) => 46308022326495007027972728677917914892729792999299745830475596687180801507328
    //0x6661696c65640000000000000000000000000000000000000000000000000000

endmodule
```
The Foundry success predicate performs the same checks that the `is_success` function from Foundry in `evm/src/executor/mod.rs`.
These checks are:
- The call to the test contract has not reverted
- DSTest's `assert*` have not failed
The last condition is implemented in the `fail()` function from the file `src/test.sol` of the `ds-test` repository, which is incuded in `forge-std`.
If a DSTest assertion should fail, the `fail()` function stores `bytes32(uint256(0x01))` at the storage slot `bytes32("failed")`. Hence, checking if a DSTest `assert` has failed amounts to reading as a boolean the data from that particular storage slot.
It should also be checked if the code present in the `FoundryCheat` account is non-empty, and return false if it is.

```k
module FOUNDRY-SUCCESS
    imports EVM
    imports FOUNDRY-ACCOUNTS

    syntax Bool ::= "foundry_success" "(" StatusCode "," ByteArray "," Int ")" [function, klabel(foundry_success), symbol]
 // -------------------------------------------------------------------------------------
    rule foundry_success(EVMC_SUCCESS, _, 0) => true
    //requires STATUS =/=K EVMC_REVERT
    //   andBool
    rule foundry_success(_, _, _) => false [owise]
 
    //rule foundry_success() => false [owise]

    //rule [[ foundry_success() => true ]]
    //     <account>
    //         <acctID> #address(FoundryCheat) </acctID>
    //         <storage> STORAGE </storage>
    //         <code> FOUNDRY_CODE </code>
    //         ...
    //     </account>
    //     <statusCode> STATUS </statusCode>
    //     requires STATUS =/=K EVMC_REVERT
    //         andBool #sizeByteArray(FOUNDRY_CODE) >Int 0
    //         andBool #lookup(STORAGE,  #loc(FoundryCheat . Failed)) ==Int 0

endmodule
```

Foundry Cheat Codes
-------------------

```k
module FOUNDRY-CHEAT-CODES
    imports EVM
    imports FOUNDRY-ACCOUNTS

    syntax KItem ::= "#assert" "(" Bool ")" | "#assume" "(" Bool ")"
    //--------------------------------------------------------------
    rule <k> #assert(false) => . ... </k>
         <account>
             <acctID> #address(FoundryCheat) </acctID>
             <storage> ... #loc(FoundryCheat . Failed) |-> (_ => 1) ... </storage>
             ...
         </account>
    


    syntax CheatCodes ::= "assertTrue" "(" Bool ")" [klabel(assertTrue)]
    //------------------------------------------------------------------
    rule <k> assertTrue(false) </k>
         <account>
             <acctID> #address(FoundryCheat) </acctID>
             <storage> ... #loc(FoundryCheat . Failed) |-> (_ => 1) ... </storage>
             ...
         </account>

     syntax CheatCodes ::= "assertLt" "(" Int "," Int ")" [klabel(assertLt)]
     //--------------------------------------------------
     rule <k> assertLt(N, M) </k>
          <account>
             <acctID> #address(FoundryCheat) </acctID>
             <storage> ... #loc(FoundryCheat . Failed) |-> (_ => 1) ... </storage>
             ...
         </account>
         requires notBool N <Int M

endmodule
```

