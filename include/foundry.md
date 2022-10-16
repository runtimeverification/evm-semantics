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
requires "abi.md"
requires "edsl.md"

module FOUNDRY
    imports FOUNDRY-SUCCESS
    imports FOUNDRY-CHEAT-CODES
    imports FOUNDRY-ACCOUNTS
    imports EDSL

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

    syntax Int             ::= #address ( Contract ) [macro]
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
    imports EVM-ABI
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

#### Structure of execution

The `foundry.call` rule is used to inject specific behaviour for each cheat code.
The rule has a higher priority than any other `CALL` rule and will match every call made to the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
The function selector, represented as `#asWord(#range(LM, ARGSTART, 4))` and the call data `#range(LM, ARGSTART +Int 4, ARGWIDTH -Int 4)` are passed to the `#call_foundry` production, which will further rewrite using rules defined for implemented cheat codes.
Finally, the rule for `#return_foundry` is used to end the execution of the `CALL` OpCode.

```{.k .bytes}
    rule [foundry.call]:
         <k> CALL _ CHEAT_ADDR _VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
          => #call_foundry #asWord(#range(LM, ARGSTART, 4)) #range(LM, ARGSTART +Int 4, ARGWIDTH -Int 4)
          ~> #return_foundry RETSTART RETWIDTH
         ...
         </k>
         <localMem> LM </localMem>
         <output> _ => .ByteArray </output>
    requires CHEAT_ADDR ==Int #address(FoundryCheat)
    [priority(40)]
```

We define two productions named `#return_foundry` and `#call_foundry`, which will be used by each cheat code.
The rule `foundry.return` will rewrite the `#return_foundry` production into other productions that will place the output of the execution into the local memory, refund the gas value of the call and push the value `1` on the call stack.

```{.k .bytes}
    syntax KItem ::= "#error_foundry" [klabel(foundry_error)]
                   | "#return_foundry" Int Int [klabel(foundry_return)]
                   | "#call_foundry" Int ByteArray [klabel(foundry_call)]
 // ---------------------------------------------------------------------
    rule [foundry.return]:
         <k> #return_foundry RETSTART RETWIDTH
          => #setLocalMem RETSTART RETWIDTH OUT
          ~> #refund GCALL
          ~> 1 ~> #push
          ... </k>
         <output> OUT </output>
         <callGas> GCALL </callGas>
```

Below, we define rules for the `#call_foundry` production, handling the cheat codes.

#### `assume` - Insert a condition

```
function assume(bool) external;
```

`foundry.call.assume` will match when the `assume` cheat code function is called.
This rule then takes a `bool` condition from the function call data, represented using the `ARGS` variable, and injects it into the execution path using the `#assume` production.
`==K #bufStrict(32, 1)` is used to mark that the condition should hold.

```{.k .bytes}
    rule [foundry.call.assume]:
         <k> #call_foundry SELECTOR ARGS => #assume(ARGS ==K #bufStrict(32, 1)) ... </k>
      requires SELECTOR ==Int selector ( "assume(bool)" )
```

#### `deal` - Set a given balance to a given account.

```
function deal(address who, uint256 newBalance) external;
```

`foundry.call.deal` will match when the `deal` cheat code function is called.
The rule then takes from the function call data the target account, using `#asWord(#range(ARGS, 0, 32)`, and the new balance, using `#asWord(#range(ARGS, 32, 32))`, and forwards them to the `#setBalance` production which updates the account accordingly.

```{.k .bytes}
    rule [foundry.call.deal]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(#range(ARGS, 0, 32)) ~> #setBalance #asWord(#range(ARGS, 0, 32)) #asWord(#range(ARGS, 32, 32)) ... </k>
      requires SELECTOR ==Int selector ( "deal(address,uint256)" )
```

#### `etch` - Sets the code of an account.

```
function etch(address who, bytes calldata code) external;
```

`foundry.call.etch` will match when the `etch` cheat code function is called.
This rule then takes from the function call data the target account, using `#asWord(#range(ARGS, 0, 32)`, and the new bytecode, using `#range(ARGS, CODE_START, CODE_LENGTH)`, where `#asWord(#range(ARGS, 64, 32))` is used to determine the length of the second argument.
The values are forwarded to the `#setCode` production which updates the account accordingly.

```{.k .bytes}
    rule [foundry.call.etch]:
         <k> #call_foundry SELECTOR ARGS
          => #loadAccount #asWord(#range(ARGS, 0, 32))
          ~> #let CODE_START = 96 #in
             #let CODE_LENGTH = #asWord(#range(ARGS, 64, 32)) #in
             #setCode #asWord(#range(ARGS, 0, 32)) #range(ARGS, CODE_START, CODE_LENGTH)
         ...
         </k>
      requires SELECTOR ==Int selector ( "etch(address,bytes)" )
```

#### `warp` - Sets the block timestamp.

```
function warp(uint256) external;
```

`foundry.call.warp` will match when the `warp` cheat code function is called.
This rule then takes the `uint256` value from the function call data which is represented as `ARGS` and updates the `<timestamp>` cell.

```{.k .bytes}
    rule [foundry.call.warp]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <timestamp> _ => #asWord(ARGS) </timestamp>
      requires SELECTOR ==Int selector( "warp(uint256)" )
```

#### `roll` - Sets the block number.

```
function roll(uint256) external;
```

`foundry.call.roll` will match when the `roll` cheat code function is called.
This rule then takes the `uint256` value from the function call data which is represented as `ARGS` and updates the `<number>` cell.

```{.k .bytes}
    rule [foundry.call.roll]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <number> _ => #asWord(ARGS) </number>
      requires SELECTOR ==Int selector ( "roll(uint256)" )
```

#### `fee` - Sets the block base fee.

```
function fee(uint256) external;
```

`foundry.call.fee` will match when the `fee` cheat code function is called.
This rule then takes the `uint256` value from the function call data which is represented as `ARGS` and updates the `<baseFee>` cell.

```{.k .bytes}
    rule [foundry.call.fee]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <baseFee> _ => #asWord(ARGS) </baseFee>
      requires SELECTOR ==Int selector ( "fee(uint256)" )
```

#### `chainId` - Sets the chain ID.

```
function chainId(uint256) external;
```

`foundry.call.chainId` will match when the `chainId` cheat code function is called.
This rule then takes the `uint256` value from the function call data which is represented as `ARGS` and updates the `<chainID>` cell.

```{.k .bytes}
    rule [foundry.call.chainId]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <chainID> _ => #asWord(ARGS) </chainID>
      requires SELECTOR ==Int selector ( "chainId(uint256)" )
```

#### `coinbase` - Sets the block coinbase.

```
function coinbase(address) external;
```

`foundry.call.coinbase` will match when the `coinbase` cheat code function is called.
This rule then takes the `uint256` value from the function call data which is represented as `ARGS` and updates the `<coinbase>` cell.

```{.k .bytes}
    rule [foundry.call.coinbase]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <coinbase> _ => #asWord(ARGS) </coinbase>
      requires SELECTOR ==Int selector ( "coinbase(address)" )
```

#### `label` - Sets a label for a given address.

```
function label(address addr, string calldata label) external;
```

`foundry.call.label` will match when the `label` cheat code function is called.
If an address is labelled, the label will show up in test traces instead of the address.
However, there is no change on the state and therefore this rule just skips the cheatcode invocation.

```{.k .bytes}
    rule [foundry.call.label]:
         <k> #call_foundry SELECTOR _ARGS => . ... </k>
      requires SELECTOR ==Int selector ( "label(address,string)" )
```

#### `getNonce` - Gets the nonce of the given account.

```
function getNonce(address account) external returns (uint64);
```

`foundry.call.getNonce` will match when the `getNonce` cheat code function is called.
This rule takes the `address` value from the function call data, which is represented as `ARGS`, and forwards it to the `#returnNonce` production, which will update the `<output>` cell with the `nonce` of the account.

```{.k .bytes}
    rule [foundry.call.getNonce]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(ARGS) ~> #returnNonce #asWord(ARGS) ... </k>
      requires SELECTOR ==Int selector ( "getNonce(address)" )
```

#### `setNonce` - Sets the nonce of the given account.

```
function setNonce(address account, uint64 nonce) external;
```

`foundry.call.setNonce` will match when the `setNonce` function is called.
This rule takes the `address` value and `uint64` value corresponding to new nonce using from the function call data, which is represented as `ARGS` forwards it to the `#setNonce` production, which will update the nonce of the account.

```{.k .bytes}
    rule [foundry.call.setNonce]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(#range(ARGS, 0, 32)) ~> #setNonce #asWord(#range(ARGS, 0, 32)) #asWord(#range(ARGS, 32, 32)) ... </k>
      requires SELECTOR ==Int selector ( "setNonce(address,uint64)" )
```

#### `addr` - Computes the address for a given private key.

```
function addr(uint256 privateKey) external returns (address);
```

`foundry.call.addr` will match when the `addr` cheat code function is called.
This rule takes `uint256` private key from the function call data, which is represented as `ARGS`, and computes the address.
The `<output>` cell will be updated with the value of the address generated from the private key using `#addrFromPrivateKey(#unparseByteStack(ARGS))`.
`#bufStrict` is used to pad the value to a length of 32.

```{.k .bytes}
    rule [foundry.call.addr]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <output> _ => #bufStrict(32, #addrFromPrivateKey(#unparseByteStack(ARGS))) </output>
      requires SELECTOR ==Int selector ( "addr(uint256)" )
```

#### `load` - Loads a storage slot from an address.

```
function load(address account, bytes32 slot) external returns (bytes32);
```

`foundry.call.load` will match when the `load` cheat code function is called.
This rule loads the storage slot identified by `#asWord(#range(ARGS, 32, 32))` (referring to `slot` argument) from account `#asWord(#range(ARGS, 0, 32))` (referring to `account`).
The value of the identified storage slot is placed in the `<output>` cell using the `#returnStorage` production.

```{.k .bytes}
    rule [foundry.call.load]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(#range(ARGS, 0, 32)) ~> #returnStorage #asWord(#range(ARGS, 0, 32)) #asWord(#range(ARGS, 32, 32)) ... </k>
      requires SELECTOR ==Int selector ( "load(address,bytes32)" )
```

#### `store` - Stores a value to an address' storage slot.

```
function store(address account, bytes32 slot, bytes32 value) external;
```

`foundry.call.store` will match when the `store` cheat code function is called.
This rule then takes from the function call data the account using `#asWord(#range(ARGS, 0, 32))` and the new slot value using `#asWord(#range(ARGS, 32, 32))` and updates the slot denoted by `#asWord(#range(ARGS, 64, 32))`.

```{.k .bytes}
    rule [foundry.call.store]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(#range(ARGS, 0, 32)) ~> #setStorage #asWord(#range(ARGS, 0, 32)) #asWord(#range(ARGS, 32, 32)) #asWord(#range(ARGS, 64, 32)) ... </k>
      requires SELECTOR ==Int selector ( "store(address,bytes32,bytes32)" )
```

Otherwise, throw an error for any other call to the Foundry contract.

```{.k .bytes}
    rule [foundry.call.owise]:
         <k> #call_foundry _ _ => #error_foundry ... </k> [owise]
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

- `#setBalance ACCTID NEWBAL` sets the balance of a given account.

```k
    syntax KItem ::= "#setBalance" Int Int [klabel(foundry_setBalance)]
 // -------------------------------------------------------------------
    rule <k> #setBalance ACCTID NEWBAL => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <balance> _ => NEWBAL </balance>
           ...
         </account>
```

- `#setCode ACCTID CODE` sets the code of a given account.

```k
    syntax KItem ::= "#setCode" Int ByteArray [klabel(foundry_setCode)]
 // -------------------------------------------------------------------
    rule <k> #setCode ACCTID CODE => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <code> _ => #if #asWord(CODE) ==Int 0 #then .ByteArray:AccountCode #else {CODE}:>AccountCode #fi </code>
           ...
         </account>
```

- `#returnNonce ACCTID` takes the nonce of a given account and places it on the `<output>` cell.

```k
    syntax KItem ::= "#returnNonce" Int [klabel(foundry_returnNonce)]
 // -----------------------------------------------------------------
    rule <k> #returnNonce ACCTID => . ... </k>
         <output> _ => #bufStrict(32, NONCE) </output>
         <account>
           <acctID> ACCTID </acctID>
           <nonce> NONCE </nonce>
           ...
         </account>
```

- `#setNonce ACCTID NONCE` takes a given account and a given nonce and update the account accordingly.

```k
     syntax KItem ::= "#setNonce" Int Int [klabel(foundry_setNonce)]
 // ----------------------------------------------------------------
    rule <k> #setNonce ACCTID NONCE => . ... </k>
         <account>
             <acctID> ACCTID </acctID>
             <nonce> _ => NONCE </nonce>
             ...
         </account>
```

- `#returnStorage ACCTID LOC` takes a storage value from a given account and places it on the `<output>` cell.

```k
    syntax KItem ::= "#returnStorage" Int Int [klabel(foundry_returnStorage)]
 // -------------------------------------------------------------------------
    rule <k> #returnStorage ACCTID LOC => . ... </k>
         <output> _ => #bufStrict(32, #lookup(STORAGE, LOC)) </output>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
```

- `#setStorage ACCTID LOC VALUE` sets a given value to a given location of an account.

```k
    syntax KItem ::= "#setStorage" Int Int Int [klabel(foundry_setStorage)]
 // -----------------------------------------------------------------------
    rule <k> #setStorage ACCTID LOC VALUE => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <storage> STORAGE => STORAGE [ LOC <- VALUE ] </storage>
             ...
         </account>
```

 - selectors for cheat code functions.

```k
    rule ( selector ( "assume(bool)" )                   => 1281615202 )
    rule ( selector ( "deal(address,uint256)" )          => 3364511341 )
    rule ( selector ( "etch(address,bytes)" )            => 3033974658 )
    rule ( selector ( "warp(uint256)" )                  => 3856056066 )
    rule ( selector ( "roll(uint256)" )                  => 528174896  )
    rule ( selector ( "fee(uint256)" )                   => 968063664  )
    rule ( selector ( "chainId(uint256)" )               => 1078582738 )
    rule ( selector ( "coinbase(address)" )              => 4282924116 )
    rule ( selector ( "label(address,string)" )          => 3327641368 )
    rule ( selector ( "getNonce(address)" )              => 755185067  )
    rule ( selector ( "addr(uint256)" )                  => 4288775753 )
    rule ( selector ( "load(address,bytes32)" )          => 1719639408 )
    rule ( selector ( "store(address,bytes32,bytes32)" ) => 1892290747 )
    rule ( selector ( "setNonce(address,uint64)" )       => 4175530839 )
```
```k
endmodule
```
