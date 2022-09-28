Foundry Specifications
======================

**UNDER CONSTRUCTION**

Example Usage
-------------

From the root of the [KEVM repository](../README.md), after having:

-   Successfully built (or installed) KEVM, and
-   Have `kevm` on `PATH`, and
-   Have stepped into the virtual environment (see the [README](../README.md)).

KEVM supports Foundry specifications via two CLI utilities, `foundry-kompile` and `foundry-prove`.
To get help, you can do `kevm foundry-kompile --help` and `kevm foundry-prove --help`.
Each command takes as input the Foundry `out/` directory.
For example, in the root of this repository, you can run:

*Build Foundry Project:*

```sh
$ cd tests/foundry
$ forge build
[⠊] Compiling...
[⠑] Compiling 44 files with 0.8.13
[⠊] Solc 0.8.13 finished in 3.58s
Compiler run successful (with warnings)

$ cd ../..
```

*Kompile to KEVM specification (inside virtual environment):*

```sh
(venv) $ kevm foundry-kompile tests/foundry/out
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Unknown range predicate for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Unsupported ABI type for method LoopsTest.method_LoopsTest_testMax, will not generate calldata sugar: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Unknown range predicate for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Unsupported ABI type for method LoopsTest.method_LoopsTest_testMaxBroken, will not generate calldata sugar: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Unknown range predicate for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Unsupported ABI type for method LoopsTest.method_LoopsTest_testSort, will not generate calldata sugar: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Unknown range predicate for type: uint256[]
WARNING 2022-09-11 15:36:00,448 kevm_pyk.solc_to_k - Unsupported ABI type for method LoopsTest.method_LoopsTest_testSortBroken, will not generate calldata sugar: uint256[]
WARNING 2022-09-11 15:36:00,449 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,449 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,449 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
WARNING 2022-09-11 15:36:00,449 kevm_pyk.solc_to_k - Using generic sort K for type: uint256[]
```

*And discharge some specific test as a proof obligation (inside virtual environment):*

```sh
(venv) $ kevm foundry-prove tests/foundry/out --test AssertTest.test_assert_true
WARNING 2022-09-11 15:37:31,956 __main__ - Ignoring command-line option: --definition: /home/dev/src/evm-semantics/.build/usr/lib/kevm/haskell
#Top
```

Foundry Module for KEVM
-----------------------

Foundry's testing framework provides a series of cheatcodes so that developers can specify what situation they want to test.
This file describes the KEVM specification of the Foundry testing framework, which includes the definition of said cheatcodes and what does it mean for a test to pass.

```k
requires "evm.md"
requires "hashed-locations.md"

module FOUNDRY
    imports FOUNDRY-SUCCESS
    imports FOUNDRY-CHEAT-CODES
    imports FOUNDRY-ACCOUNTS

    configuration
      <foundry>
        <kevm/>
        <cheatcodes/>
      </foundry>
endmodule
```

### Foundry Success Predicate

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

### Foundry Cheat Codes

The configuration of the Foundry Cheat Codes is defined as follwing:
1. The `<prank>` subconfiguration stores values which are used during the execution of any kind of `prank` cheatcode:
    - `<prevCaller>` keeps the current address of the contract that initiated the prank.
    - `<prevOrigin>` keeps the current address of the `tx.origin` value.
    - `<newCaller>` and `<newOrigin>` are addresses to be assigned after the prank call to `msg.sender` and `tx.origin`.
    - `<depth>` records the current call depth at which the prank was invoked.
    - `<singleCall>` tells whether the prank stops by itself after the next call or when a `stopPrank` cheat code is invoked.

```k
module FOUNDRY-CHEAT-CODES
    imports EVM
    imports FOUNDRY-ACCOUNTS

    configuration
      <cheatcodes>
        <prank>
          <prevCaller> .Account </prevCaller>
          <prevOrigin> .Account </prevOrigin>
          <newCaller> .Account </newCaller>
          <newOrigin> .Account </newOrigin>
          <depth> 0 </depth>
          <singleCall> false </singleCall>
        </prank>
      </cheatcodes>
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
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #assume(#range(LM, ARGSTART +Int 4, 32) ==K #bufStrict(32, 1)) ~> #finishCheatCode ... </k>
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
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #setBalance #asWord(#range(LM, ARGSTART +Int 4, 32)) #asWord(#range(LM, ARGSTART +Int 36, 32)) ~> #finishCheatCode ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 3364511341 // selector ( "deal(address,uint256)" )
      [priority(40)]

    syntax KItem ::= "#setBalance" Int Int [klabel(foundry_setBalance)]
 // -------------------------------------------------------------------
    rule <k> #setBalance ACCTID NEWBAL => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <balance> _ => NEWBAL </balance>
           ...
         </account>
```

#### `etch` - Sets the code of an account.

```
function etch(address who, bytes calldata code) external;
```

`call.etch` will match when the `etch` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the account using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and the new bytecode using `#range(LM, ARGSTART +Int 36, ARGWIDTH -Int 36)`, where `ARGWIDTH -Int 36` is used to determine the length of the second argument.
The values are forwarded to the `#setCode` marker which updates the account accordingly.

```k
    rule [call.etch]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH
          => #let CODE_START = ARGSTART +Int 100 #in
             #let CODE_LENGTH = #asWord(#range(LM, ARGSTART +Int 68, 32)) #in
             #setCode #asWord(#range(LM, ARGSTART +Int 4, 32)) #range(LM, CODE_START, CODE_LENGTH)
          ~> #finishCheatCode
         ...
         </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 3033974658 // selector ( "etch(address,bytes)" )
      [priority(40)]

    syntax KItem ::= "#setCode" Int ByteArray [klabel(foundry_setCode)]
 // -------------------------------------------------------------------
    rule <k> #setCode ACCTID CODE => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <code> _ => #if #asWord(CODE) ==Int 0 #then .ByteArray:AccountCode #else {CODE}:>AccountCode #fi </code>
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
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #finishCheatCode ... </k>
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
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #finishCheatCode ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
         <number> _ => #asWord(#range(LM, ARGSTART +Int 4, 32)) </number>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 528174896 // selector ( "roll(uint256)" )
      [priority(40)]
```

#### `fee` - Sets the block base fee.

```
function fee(uint256) external;
```

`call.fee` will match when the `fee` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the `uint256` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and updates the `<baseFee>` cell.

```k
    rule [call.fee]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #finishCheatCode ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
         <baseFee> _ => #asWord(#range(LM, ARGSTART +Int 4, 32)) </baseFee>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 968063664 // selector ( "fee(uint256)" )
      [priority(40)]
```

#### `chainId` - Sets the chain ID.

```
function chainId(uint256) external;
```

`call.chainId` will match when the `chanId` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the `uint256` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and updates the `<chainID>` cell.

```k
    rule [call.chainId]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #finishCheatCode ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
         <chainID> _ => #asWord(#range(LM, ARGSTART +Int 4, 32)) </chainID>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 1078582738 // selector ( "chainId(uint256)" )
      [priority(40)]
```

#### `coinbase` - Sets the block coinbase.

```
function coinbase(address) external;
```

`call.coinbase` will match when the `coinbase` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the `uint256` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and updates the `<coinbase>` cell.

```k
    rule [call.coinbase]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #finishCheatCode ... </k>
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
If an address is labelled, the label will show up in test traces instead of the address.
However, there is no change on the state and therefore this rule just skips the cheatcode invocation.

```k
    rule [call.label]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #finishCheatCode ... </k>
         <output> _ => .ByteArray </output>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 3327641368 // selector ( "label(address,string)" )
    [priority(40)]
```

#### `getNonce` - Gets the nonce of the given account.

```
function getNonce(address account) external returns (uint64);
```

`call.getNonce` will match when the `getNonce` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule takes the `address` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and returns its `nonce` updating the `<output>` cell.

```k
    rule [call.getNonce]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH RETSTART RETWIDTH => #returnNonce #asWord(#range(LM, ARGSTART +Int 4, 32)) RETSTART RETWIDTH ~> #finishCheatCode ... </k>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 755185067 // selector ( "getNonce(address)" )
      [priority(40)]

    syntax KItem ::= "#returnNonce" Int Int Int [klabel(foundry_returnNonce)]
 // -------------------------------------------------------------------------
    rule <k> #returnNonce ACCTID RETSTART RETWIDTH => #setLocalMem RETSTART RETWIDTH #bufStrict(32, NONCE) ... </k>
         <output> _ => #bufStrict(32, NONCE) </output>
         <account>
           <acctID> ACCTID </acctID>
           <nonce>  NONCE  </nonce>
           ...
         </account>
```

#### `addr` - Computes the address for a given private key.

```
function addr(uint256 privateKey) external returns (address);
```

`call.addr` will match when the `addr` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule takes `uint256` value using `#asWord(#range(LM, ARGSTART +Int 4, 32)` and computes the address for a given private key updating the `<output>` cell.

```k
    rule [call.addr]:
         <k> CALL _ CHEAT_ADDR _ ARGSTART _ARGWIDTH RETSTART RETWIDTH => #setLocalMem RETSTART RETWIDTH #bufStrict(32, #addrFromPrivateKey(#unparseByteStack(#range(LM, ARGSTART +Int 4, 32)))) ~> #finishCheatCode ... </k>
         <output> _ => #bufStrict(32, #addrFromPrivateKey(#unparseByteStack(#range(LM, ARGSTART +Int 4, 32)))) </output>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 4288775753 // selector ( "addr(uint256)" )
      [priority(40)]
```

#### `load` - Loads a storage slot from an address.

```
function load(address account, bytes32 slot) external returns (bytes32);
```

`call.load` will match when the `load` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then loads the storage slot identified by `#asWord(#range(LM, ARGSTART +Int 36, 32))` (referring to `slot` argument) from account `#asWord(#range(LM, ARGSTART +Int 4, 32))` (referring to `account`) and sets the return value to the loaded slot value.

```k
    rule [call.load]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH RETSTART RETWIDTH => #loadAccount #asWord(#range(LM, ARGSTART +Int 4, 32)) ~> #returnStorage #asWord(#range(LM, ARGSTART +Int 4, 32)) #asWord(#range(LM, ARGSTART +Int 36, 32)) RETSTART RETWIDTH ~> #finishCheatCode ... </k>
         <localMem> LM </localMem>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 1719639408 // selector ( "load(address,bytes32)" )
      [priority(40)]

    syntax KItem ::= "#returnStorage" Int Int Int Int [klabel(foundry_returnStorage)]
 // ---------------------------------------------------------------------------------
    rule <k> #returnStorage ACCTID LOC RETSTART RETWIDTH => #setLocalMem RETSTART RETWIDTH #bufStrict(32, #lookup(STORAGE, LOC)) ... </k>
         <output> _ => #bufStrict(32, #lookup(STORAGE, LOC)) </output>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
```

#### `store` - Stores a value to an address' storage slot.

```
function store(address account, bytes32 slot, bytes32 value) external;
```

`call.store` will match when the `store` function is called at the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
This rule then takes the account using `#asWord(#range(LM, ARGSTART +Int 4, 32))` and the new slot value using `#asWord(#range(LM, ARGSTART +Int 68, 32))` and updates the slot denoted by `#asWord(#range(LM, ARGSTART +Int 36, 32))`.

```k
    rule [call.store]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART _ARGWIDTH _RETSTART _RETWIDTH => #loadAccount #asWord(#range(LM, ARGSTART +Int 4, 32)) ~> #setStorage #asWord(#range(LM, ARGSTART +Int 4, 32)) #asWord(#range(LM, ARGSTART +Int 36, 32)) #asWord(#range(LM, ARGSTART +Int 68, 32)) ~> #finishCheatCode ... </k>
         <localMem> LM </localMem>
         <output> _ => .ByteArray </output>
      requires CHEAT_ADDR ==Int #address(FoundryCheat)
       andBool #asWord(#range(LM, ARGSTART, 4)) ==Int 1892290747 // selector ( "store(address,bytes32,bytes32)" )
      [priority(40)]

    syntax KItem ::= "#setStorage" Int Int Int [klabel(foundry_setStorage)]
 // -----------------------------------------------------------------------
    rule <k> #setStorage ACCTID LOC VALUE => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE => STORAGE [ LOC <- VALUE ] </storage>
             ...
         </account>
```

Utils
-----

- `#loadAccount ACCT` creates a new, empty account for `ACCT` if it does not already exist. Otherwise, it has no effect

```k
    syntax KItem ::= "#loadAccount" Int [klabel(foundry_loadAccount)]
 // -----------------------------------------------------------------
    rule <k> #loadAccount ACCT => #accessAccounts ACCT ... </k>
         <activeAccounts> ACCTS:Set </activeAccounts>
      requires ACCT in ACCTS

    rule <k> #loadAccount ACCT => #newAccount ACCT ~> #accessAccounts ACCT ... </k>
         <activeAccounts> ACCTS:Set </activeAccounts>
      requires notBool ACCT in ACCTS
```

- `#finishCheatCode` is a production used to group togheter productions which are used on every cheat code.

```k
    syntax KItem ::= "#finishCheatCode" [klabel(foundry_finishCheatCode)]
 // ---------------------------------------------------------------------
    rule <k> #finishCheatCode => 1 ~> #push ~> #refund GCALL ... </k>
         <callGas> GCALL => 0 </callGas>
```

```k
endmodule
```
