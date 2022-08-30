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
    imports FOUNDRY-ACCOUNTS
endmodule
```

Foundry Success Predicate
-------------------------

Foundry has several baked-in convenience accounts for helping to define the "cheat-codes".
Here we define their addresses, and important storage-locations.

```k
module FOUNDRY-ACCOUNTS
    imports SOLIDITY-FIELDS

    syntax Contract        ::= FoundryContract
    syntax Field           ::= FoundryField
    syntax FoundryContract ::= "Foundry"      [klabel(contract_Foundry)]
                             | "FoundryTest"  [klabel(contract_FoundryTest)]
                             | "FoundryCheat" [klabel(contract_FoundryCheat)]
 // -------------------------------------------------------------------------
    rule #address(Foundry)      => 137122462167341575662000267002353578582749290296  // 0x1804c8AB1F12E6bbf3894d4083f33e07309d1f38
    rule #address(FoundryTest)  => 1032069922050249630382865877677304880282300743300 // 0xb4c79daB8f259C7Aee6E5b2Aa729821864227e84
    rule #address(FoundryCheat) => 645326474426547203313410069153905908525362434349  // 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D

    syntax FoundryField ::= "Failed" [klabel(slot_failed)]
 // ------------------------------------------------------
    rule #loc(FoundryCheat . Failed) => 46308022326495007027972728677917914892729792999299745830475596687180801507328 // 0x6661696c65640000000000000000000000000000000000000000000000000000

endmodule
```

The Foundry success predicate performs the same checks as [the `is_success` function from Foundry in `evm/src/executor/mod.rs`](https://github.com/foundry-rs/foundry/blob/e530c7325816e4256f62f4426bd9985dc54da831/evm/src/executor/mod.rs#L490).

These checks are:

-   The call to the test contract has not reverted, and
-   `DSTest.assert*` have not failed.

The last condition is implemented in the [`fail()` function from `DSTest`](https://github.com/dapphub/ds-test/blob/9310e879db8ba3ea6d5c6489a579118fd264a3f5/src/test.sol#L65).
If a DSTest assertion should fail, the `fail()` function stores `bytes32(uint256(0x01))` at the storage slot `bytes32("failed")`.
Hence, checking if a `DSTest.assert*` has failed amounts to reading as a boolean the data from that particular storage slot.

**TODO**: It should also be checked if the code present in the `FoundryCheat` account is non-empty, and return false if it is.

```k
module FOUNDRY-SUCCESS
    imports EVM

    syntax Bool ::= "foundry_success" "(" StatusCode "," Int ")" [function, klabel(foundry_success), symbol]
 // --------------------------------------------------------------------------------------------------------
    rule foundry_success(EVMC_SUCCESS, 0) => true
    rule foundry_success(_, _)            => false [owise]

endmodule
```

Foundry Cheat Codes
-------------------

```k
module FOUNDRY-CHEAT-CODES
    imports EVM
    imports FOUNDRY-ACCOUNTS
```

First we have some helpers in K which can:

-   Inject a given boolean condition into's this execution's path condition, and
-   Check that a given boolean condition holds (recording failure if not).

```k
    syntax KItem ::= #assume ( Bool ) [klabel(foundry_assume), symbol]
                   | #assert ( Bool ) [klabel(foundry_assert), symbol]
 // ------------------------------------------------------------------
    rule <k> #assume(B) => . ... </k> ensures B

    rule <k> #assert(false) => . ... </k>
         <account>
             <acctID> #address(FoundryCheat) </acctID>
             <storage> STORAGE => STORAGE [ #loc(FoundryCheat . Failed) <- 1 ] </storage>
             ...
         </account>
```

#### `deal` - Set a given balance to a given account.

```
function deal(address who, uint256 newBalance) external;
```

`call.deal` will match when the `deal` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the account using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and the new balance using `#asWord(#range(LM, ARGSTART +Int 36, 32))` and forwards them to the `#setBalance` marker which updates the account accordingly.

```k
    rule [call.deal]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0
          => #setBalance(#asWord(#range(LM, ARGSTART +Int 4, 32)), #asWord(#range(LM, ARGSTART +Int 36, 32)))
          ~> 1 ~> #push
         ...
         </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 3364511341 // selector ( "deal" )
      [priority(40)]

    syntax KItem ::= "#setBalance" "(" Int "," Int ")" [klabel(foundry_setBalance)]
 // -------------------------------------------------------------------------------
    rule <k> #setBalance(ACCTID, NEWBAL) => . ... </k>
         <account>
             <acctID> ACCTID </acctID>
             <balance> _ => NEWBAL </balance>
             ...
         </account>
```

```k
endmodule
```

