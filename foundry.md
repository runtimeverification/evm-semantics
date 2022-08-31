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

#### `assume` - Insert a condition

```
function assume(bool) external;
```

`call.assume` will match when the `assume` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes a `bool` condition using `#range(LM, ARGSTART +Int 4, 32)` and injects it into the execution path using the `#assume` production.
`==K #bufStrict(32, 1)` is used to mark that the condition should hold.
```k

    rule [call.assume]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0 => #assume(#range(LM, ARGSTART +Int 4, 32) ==K #bufStrict(32, 1)) ~> 1 ~> #push ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 1281615202 // selector ( "assume(bool)" )
      [priority(40)]
```

#### `deal` - Set a given balance to a given account.

```
function deal(address who, uint256 newBalance) external;
```

`call.deal` will match when the `deal` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the account using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and the new balance using `#asWord(#range(LM, ARGSTART +Int 36, 32))` and forwards them to the `#setBalance` marker which updates the account accordingly.

```k
    rule [call.deal]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0 => #setBalance(#asWord(#range(LM, ARGSTART +Int 4, 32)), #asWord(#range(LM, ARGSTART +Int 36, 32))) ~> 1 ~> #push ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 3364511341 // selector ( "deal(address,uint256)" )
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

#### `warp` - Sets the block timestamp.

```
function warp(uint256) external;
```

`call.warp` will match when the `warp` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the uint256 value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and updates the `<timestamp>` cell.

```k
    rule [call.warp]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0 => 1 ~> #push ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
         <timestamp> _ => #asWord(#range(LM, ARGSTART +Int 4, 32)) </timestamp>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 3856056066 // selector ( "warp(uint256)" )
      [priority(40)]
```

#### `roll` - Sets the block number.

```
function roll(uint256) external;
```

`call.roll` will match when the `roll` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the `uint256` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and updates the `<number>` cell.

```k
    rule [call.roll]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0 => 1 ~> #push ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
         <number> _ => #asWord(#range(LM, ARGSTART +Int 4, 32)) </number>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 528174896 // selector ( "roll(uint256)" )
      [priority(40)]
```

#### `fee` - Sets the block number.

```
function fee(uint256) external;
```

`call.fee` will match when the `fee` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the `uint256` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and updates the `<baseFee>` cell.

```k
    rule [call.fee]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0 => 1 ~> #push ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
         <baseFee> _ => #asWord(#range(LM, ARGSTART +Int 4, 32)) </baseFee>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 968063664 // selector ( "fee(uint256)" )
      [priority(40)]
```

#### `chainId` - Sets the block number.

```
function chainId(uint256) external;
```

`call.chainId` will match when the `chanId` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the `uint256` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and updates the `<chainID>` cell.

```k
    rule [call.chainId]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0 => 1 ~> #push ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
         <chainID> _ => #asWord(#range(LM, ARGSTART +Int 4, 32)) </chainID>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 1078582738 // selector ( "chainId(uint256)" )
      [priority(40)]
```

#### `coinbase` - Sets the block number.

```
function coinbase(address) external;
```

`call.coinbase` will match when the `coinbase` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the `uint256` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and updates the `<coinbase>` cell.

```k
    rule [call.coinbase]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0 => 1 ~> #push ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
         <coinbase> _ => #asWord(#range(LM, ARGSTART +Int 4, 32)) </coinbase>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 4282924116 // selector ( "coinbase(address)" )
      [priority(40)]

```
#### `label` - Sets a label for a given address.

```
function label(address addr, string calldata label) external;
```

`call.label` will match when the `label` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
If an address is labelled, the label will show up in test traces instead of the address. However, there is no change on the state and therefore this rule just skips the cheatcode invocation. 

```k
    rule [call.label]:
         <k> CALL _ CHEAT_ADDR 0 ARGSTART _ARGWIDTH 0 0 => 1 ~> #push ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 3327641368 // selector ( "label(address,string)" )


```k
endmodule
```

