Foundry Specifications
======================

**ACTIVE DEVELOPMENT**

The Foundry integration allows users to take Solidity property tests and generate K specifications which can be executed using the Haskell symbolic backend.

Before executing any of the KEVM instructions, make sure that you have the following:
   1. Successfully built or installed KEVM,
   2. The`kevm` binary is on your PATH,
   3. Activated the virtual environment (*applicable only for builds from source*).

Below we are providing an example usage and a description of all the commands you can use with KEVM to improve your experience.

Available Commands
------------------

Basic commands are (and each can be passed `--help`):

- `kevm foundry-kompile`: Kompile a definition, generating claims for each Foundry test.
  The best options are:
   - `--regen` - needed if Solidity sources change,
   - `--rekompile` - needed if K lemmas change, or K definition changes,
   - `--require` - for adding an extra K file with lemmas,
   - `--module-import` - importing an extra K module in one of the added K files with lemmas.

- `kevm foundry-prove`: Run a given proof using the KCFG-based prover (not supporting loops yet, need to fall back to typical K for that).
  The best options are:
   - `--reinit` - want to start over from scratch,
   - `--no-simplify-init` - do not want to invoke simplification on all the original nodes, can be faster,
   - `--max-depth` - increase the space between saved nodes; bigger is faster,
   - `--max-iterations` - maximum number of nodes to store in KCFG before giving on attempting proof for that run,
   - `--break-every-step` - save a state every opcode, slow, good for debugging,
   - `--break-on-calls` - save a state every time a call is made, good to turn on.
   - `--verbose` - output what the prover is doing to make sure it's making progress.

- `kevm foundry-show`: Display the given KCFG so far as text.
  Options are:
   - `--no-minimize` - do not omit all the gory details,
   - `--node` - can be a repeated option, display more information about a given node hash,
   - `--node-delta` - displays the delta between two given nodes in the KCFG.

- `kevm foundry-view-kcfg`: Launch the more interactive exploration of the KCFG (can be done while exploration is running, must Ctrl-C + relaunch to view updates to KCFG).
   - The interactive KCFG puts your terminal in *application mode*. To select text in this mode, hold the modifier key provided by your terminal emulator (typically SHIFT or OPTION) while clicking and dragging. Refer to the [Textualize documentation](https://github.com/Textualize/textual/blob/main/FAQ.md#how-can-i-select-and-copy-text-in-a-textual-app) for more information.

- `kevm foundry-section-edge`: Given an edge in the graph, cut it into sections to get intermediate nodes.

- `kevm foundry-step-node`: Step from a given node, adding it to the CFG.

- `kevm foundry-simplify-node`: Simplify a given node, and potentially replace it.

Example Usage
-------------

The first step is to ensure the Solidity codebase is compiled and the `out/` directory is generated.

For example, in the root of this repository, you can run:

*Build Foundry Project:*

```sh
$ cd tests/foundry
$ forge build
```

*Kompile to generate K specifications:*

```sh
$ kevm foundry-kompile
```

*And discharge some specific test as a proof obligation (inside virtual environment):*

```sh
$ kevm foundry-prove --test AssertTest.test_assert_true
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
requires "lemmas/lemmas.k"

module FOUNDRY
    imports FOUNDRY-SUCCESS
    imports FOUNDRY-CHEAT-CODES
    imports FOUNDRY-ACCOUNTS
    imports EDSL
    imports LEMMAS

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
    syntax FoundryContract ::= "FoundryTest"  [klabel(contract_FoundryTest)]
                             | "FoundryCheat" [klabel(contract_FoundryCheat)]
 // -------------------------------------------------------------------------
    rule #address(FoundryTest)  => 728815563385977040452943777879061427756277306518  // 0x7FA9385bE102ac3EAc297483Dd6233D62b3e1496
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

    syntax Bool ::= 
      "foundry_success" "("
        statusCode: StatusCode "," 
        failed: Int ","
        revertExpected: Bool ","
        opcodeExpected: Bool ","
        recordEventExpected: Bool ","
        eventExpected: Bool
      ")" [function, klabel(foundry_success), symbol]
 // -------------------------------------------------
    rule foundry_success(EVMC_SUCCESS, 0, false, false, false, false) => true
    rule foundry_success(_, _, _, _, _, _)                            => false [owise]

endmodule
```

### Foundry Cheat Codes

The configuration of the Foundry Cheat Codes is defined as follwing:
1. The `<prank>` subconfiguration stores values which are used during the execution of any kind of `prank` cheat code:
    - `<prevCaller>` keeps the current address of the contract that initiated the prank.
    - `<prevOrigin>` keeps the current address of the `tx.origin` value.
    - `<newCaller>` and `<newOrigin>` are addresses to be assigned after the prank call to `msg.sender` and `tx.origin`.
    - `<active>` signals if a prank is active or not.
    - `<depth>` records the current call depth at which the prank was invoked.
    - `<singleCall>` tells whether the prank stops by itself after the next call or when a `stopPrank` cheat code is invoked.
2. The `<expectedRevert>` subconfiguration stores values used for the `expectRevert` cheat code.
    - `<isRevertExpected>` flags if the next call is expected to revert or not.
    - `<expectedDepth>` records the depth at which the call is expected to revert.
    - `<expectedReason>` keeps the expected revert message as a `Bytes`.
3. The `<expectOpcode>` subconfiguration stores values used for `expect*OPCODE*` cheat codes.
    - `<isOpcodeExpected>` flags if a call opcode is expected.
    - `<expectedAddress>` keeps the expected caller.
    - `<expectedValue>` keeps expected `msg.value`.
    - `<expectedData>` keeps expected `calldata`.
    - `<opcodeType>` keeps track of what `CALL*` Opcode is expected.
4. The `<expectEmit>` subconfiguration stores values used for the `expectEmit` cheat code.
    - `<recordEvent>` flags if the next emitted Event should be recorded and held for future matches.
    - `<isEventExpected>` flags if an Event is expected to match the one recorded previously.
    - `<checkedTopics>` will store a list of `bool` values that flag if a topic should be checked or not.
    - `<checkedData>` flags if the data field should be checked or not.
    - `<expectedEventAddress>` stores the emitter of an expected Event.
5. The `<whitelist>` subconfiguration stores addresses that can be called and storage slots that can be accessed/modified during the execution.
    - `<isCallWhitelistActive>` flags if the whitelist mode is enabled for calls.
    - `<isStorageWhitelistActive>` flags if the whitelist mode is enabled for storage changes.
    - `<addressSet>` - stores the address whitelist.
    - `<storageSlotSet>` - stores the storage whitelist containing pairs of addresses and storage indexes.

```k
module FOUNDRY-CHEAT-CODES
    imports EVM
    imports EVM-ABI
    imports FOUNDRY-ACCOUNTS
    imports INFINITE-GAS

    configuration
      <cheatcodes>
        <prank>
          <prevCaller> .Account </prevCaller>
          <prevOrigin> .Account </prevOrigin>
          <newCaller> .Account </newCaller>
          <newOrigin> .Account </newOrigin>
          <active> false </active>
          <depth> 0 </depth>
          <singleCall> false </singleCall>
        </prank>
        <expectedRevert>
          <isRevertExpected> false </isRevertExpected>
          <expectedReason> .Bytes </expectedReason>
          <expectedDepth> 0 </expectedDepth>
        </expectedRevert>
        <expectedOpcode>
          <isOpcodeExpected> false </isOpcodeExpected>
          <expectedAddress> .Account </expectedAddress>
          <expectedValue> 0 </expectedValue>
          <expectedData> .Bytes </expectedData>
          <opcodeType> .OpcodeType </opcodeType>
        </expectedOpcode>
        <expectEmit>
          <recordEvent> false </recordEvent>
          <isEventExpected> false </isEventExpected>
          <checkedTopics> .List </checkedTopics>
          <checkedData> false </checkedData>
          <expectedEventAddress> .Account </expectedEventAddress>
        </expectEmit>
        <whitelist>
          <isCallWhitelistActive> false </isCallWhitelistActive>
          <isStorageWhitelistActive> false </isStorageWhitelistActive>
          <addressSet> .Set </addressSet>
          <storageSlotSet> .Set </storageSlotSet>
        </whitelist>
      </cheatcodes>
```

First we have some helpers in K which can:

-   Inject a given boolean condition into's this execution's path condition
-   Set the `FoundryCheat . Failed` location to `True`.
```k
    syntax KItem ::= #assume ( Bool ) [klabel(foundry_assume), symbol]
 // ------------------------------------------------------------------
    rule <k> #assume(B) => . ... </k> ensures B

     syntax KItem ::= "#markAsFailed" [klabel(foundry_markAsFailed)]
  // ---------------------------------------------------------------
     rule <k> #markAsFailed => . ... </k>
          <account>
             <acctID> #address(FoundryCheat) </acctID>
             <storage> STORAGE => STORAGE [ #loc(FoundryCheat . Failed) <- 1 ] </storage>
             ...
           </account>
```

#### Structure of execution

The `foundry.call` rule is used to inject specific behaviour for each cheat code.
The rule has a higher priority than any other `#call` rule and will match every call made to the [Foundry cheatcode address](https://book.getfoundry.sh/cheatcodes/#cheatcodes-reference).
The function selector, represented as `#asWord(#range(ARGS, 0, 4))` and the call data `#range(ARGS, 4, lengthBytes(ARGS) -Int 4)` are passed to the `#call_foundry` production, which will further rewrite using rules defined for implemented cheat codes.
Finally, the rule for `#return_foundry` is used to end the execution of the `CALL` OpCode.

```k
    rule [foundry.call]:
         <k> (#checkCall _ _
          ~> #call _ CHEAT_ADDR _ _ _ ARGS _
          ~> #return RETSTART RETWIDTH )
          => #call_foundry #asWord(#range(ARGS, 0, 4)) #range(ARGS, 4, lengthBytes(ARGS) -Int 4)
          ~> #return_foundry RETSTART RETWIDTH
         ...
         </k>
         <output> _ => .Bytes </output>
    requires CHEAT_ADDR ==Int #address(FoundryCheat)
    [priority(40)]
```

We define two productions named `#return_foundry` and `#call_foundry`, which will be used by each cheat code.
The rule `foundry.return` will rewrite the `#return_foundry` production into other productions that will place the output of the execution into the local memory, refund the gas value of the call and push the value `1` on the call stack.

```k
    syntax KItem ::= "#return_foundry" Int Int  [klabel(foundry_return)]
                   | "#call_foundry" Int Bytes  [klabel(foundry_call)]
                   | "#error_foundry" Int Bytes [klabel(foundry_error)]
 // -------------------------------------------------------------------
    rule [foundry.return]:
         <k> #return_foundry RETSTART RETWIDTH
          => #setLocalMem RETSTART RETWIDTH OUT
          ~> #refund GCALL
          ~> 1 ~> #push
          ... </k>
         <output> OUT </output>
         <callGas> GCALL </callGas>
```

We define a new status codes:
 - `FOUNDRY_UNIMPLEMENTED`, which signals that the execution ran into an unimplemented cheat code.
 - `FOUNDRY_WHITELISTCALL`, which signals that an address outside the whitelist has been called during the execution.
 - `FOUNDRY_WHITELISTSTORAGE`, which signals that a storage index of an address outside the whitelist has been changed during the execution.

```k
    syntax ExceptionalStatusCode ::= "FOUNDRY_UNIMPLEMENTED"
                                   | "FOUNDRY_WHITELISTCALL"
                                   | "FOUNDRY_WHITELISTSTORAGE"
 // -----------------------------------------------------------
```

Below, we define rules for the `#call_foundry` production, handling the cheat codes.

#### `assume` - Insert a condition

```
function assume(bool) external;
```

`foundry.call.assume` will match when the `assume` cheat code function is called.
This rule then takes a `bool` condition from the function call data, represented using the `ARGS` variable, and injects it into the execution path using the `#assume` production.
`==K #bufStrict(32, 1)` is used to mark that the condition should hold.

```k
    rule [foundry.call.assume]:
         <k> #call_foundry SELECTOR ARGS => #assume(ARGS ==K #bufStrict(32, 1)) ... </k>
      requires SELECTOR ==Int selector ( "assume(bool)" )
      [preserves-definedness]
```

#### `deal` - Set a given balance to a given account.

```
function deal(address who, uint256 newBalance) external;
```

`foundry.call.deal` will match when the `deal` cheat code function is called.
The rule then takes from the function call data the target account, using `#asWord(#range(ARGS, 0, 32)`, and the new balance, using `#asWord(#range(ARGS, 32, 32))`, and forwards them to the `#setBalance` production which updates the account accordingly.

```k
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

```k
    rule [foundry.call.etch]:
         <k> #call_foundry SELECTOR ARGS
          => #loadAccount #asWord(#range(ARGS, 0, 32))
          ~> #setCode #asWord(#range(ARGS, 0, 32)) #range(ARGS, 96, #asWord(#range(ARGS, 64, 32)))
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

```k
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

```k
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

```k
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

```k
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

```k
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

```k
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

```k
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

```k
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
The `<output>` cell will be updated with the value of the address generated from the private key, padded to 32 bytes wide.

```k
    rule [foundry.call.addr]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <output> _ => #bufStrict(32, #addrFromPrivateKey(#unparseDataBytes(ARGS))) </output>
      requires SELECTOR ==Int selector ( "addr(uint256)" )
```

#### `load` - Loads a storage slot from an address.

```
function load(address account, bytes32 slot) external returns (bytes32);
```

`foundry.call.load` will match when the `load` cheat code function is called.
This rule loads the storage slot identified by `#asWord(#range(ARGS, 32, 32))` (referring to `slot` argument) from account `#asWord(#range(ARGS, 0, 32))` (referring to `account`).
The value of the identified storage slot is placed in the `<output>` cell using the `#returnStorage` production.

```k
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

```k
    rule [foundry.call.store]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(#range(ARGS, 0, 32)) ~> #setStorage #asWord(#range(ARGS, 0, 32)) #asWord(#range(ARGS, 32, 32)) #asWord(#range(ARGS, 64, 32)) ... </k>
      requires SELECTOR ==Int selector ( "store(address,bytes32,bytes32)" )
```

#### `symbolicStorage` - Makes the storage of the given address completely symbolic.

```
function symbolicStorage(address) external;
```

`foundry.call.symbolicStorage` will match when the `symbolicStorage` cheat code function is called.
This rule then takes the address using `#asWord(#range(ARGS, 0, 32))` and makes its storage completely symbolic.

```k
    rule [foundry.call.symbolicStorage]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(ARGS) ~> #setSymbolicStorage #asWord(ARGS) ... </k>
      requires SELECTOR ==Int selector ( "symbolicStorage(address)" )
```

#### `freshUInt` - Returns a single symbolic unsigned integer.

```
function freshUInt(uint8) external returns (uint256);
```

`foundry.call.freshUInt` will match when the `freshUInt` cheat code function is called.
This rule returns a symbolic integer of up to the bit width that was sent as an argument.

```{.k .symbolic}
    rule [foundry.call.freshUInt]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <output> _ => #bufStrict(32, ?WORD) </output>
      requires SELECTOR ==Int selector ( "freshUInt(uint8)" )
       andBool 0 <Int #asWord(ARGS) andBool #asWord(ARGS) <=Int 32
       ensures 0 <=Int ?WORD andBool ?WORD <Int 2 ^Int (8 *Int #asWord(ARGS))
```

#### `freshBool` - Returns a single symbolic boolean.

```
function freshBool() external returns (bool);
```

`foundry.call.freshBool` will match when the `freshBool` cheat code function is called.
This rule returns a symbolic boolean value being either 0 (false) or 1 (true).

```{.k .symbolic}
    rule [foundry.call.freshBool]:
         <k> #call_foundry SELECTOR _ => . ... </k>
         <output> _ => #bufStrict(32, ?WORD) </output>
      requires SELECTOR ==Int selector ( "freshBool()" )
       ensures #rangeBool(?WORD)
```

Expecting the next call to revert
---------------------------------

```
function expectRevert() external;
function expectRevert(bytes4 msg) external;
function expectRevert(bytes calldata msg) external;
```

All cheat code calls which take place while `expectRevert` is active are ignored.

```k
    rule [foundry.call.ignoreCalls]:
         <k> #call_foundry _ _ => . ... </k>
         <expectedRevert>
           <isRevertExpected> true </isRevertExpected>
           ...
         </expectedRevert>
      [priority(35)]
```

The `#halt` production is used to examine the end of each call in KEVM.
If the call depth of the current call is lower than the call depth of the `expectRevert` cheat code and the `<statusCode>` is not `EVMC_SUCCESS`, the `#checkRevertReason` will be used to compare the output of the call with the expect reason provided.

```k
    rule [foundry.handleExpectRevert]:
         <k> (. => #checkRevertReason ~> #clearExpectRevert) ~> #halt ... </k>
         <statusCode> SC </statusCode>
         <callDepth> CD </callDepth>
         <expectedRevert>
           <isRevertExpected> true </isRevertExpected>
           <expectedDepth> ED </expectedDepth>
           ...
         </expectedRevert>
      requires CD <=Int ED
       andBool SC =/=K EVMC_SUCCESS
      [priority(40)]
```

If the call is successful, a revert is triggered and the `FAILED` location of the `Foundry` contract is set to `true` using `#markAsFailed`.

```k
    rule [foundry.handleExpectRevert.error]:
         <k> (. => #markAsFailed ~> #clearExpectRevert) ~> #halt ... </k>
         <statusCode> EVMC_SUCCESS => EVMC_REVERT </statusCode>
         <callDepth> CD </callDepth>
         <expectedRevert>
           <isRevertExpected> true </isRevertExpected>
           <expectedDepth> ED </expectedDepth>
           ...
         </expectedRevert>
      requires CD <=Int ED
      [priority(40)]
```

If the `expectRevert()` selector is matched, call the `#setExpectRevert` production to initialize the `<expectedRevert>` subconfiguration.

```k
    rule [foundry.call.expectRevert]:
         <k> #call_foundry SELECTOR ARGS => #setExpectRevert ARGS ... </k>
      requires SELECTOR ==Int selector ( "expectRevert()" )
        orBool SELECTOR ==Int selector ( "expectRevert(bytes)" )
```

Expecting a specific CALL/CREATE opcode
---------------------------------------

First we define a sort to identify expected opcodes.

```k
    syntax OpcodeType ::= ".OpcodeType" | "Call" | "Static" | "Delegate" | "Create" | "Create2"
```

If the `expect*OPCODE*` selector is matched, the rule will load the account into the state and add the `#setExpectOpcode` production to the K cell to initialize the `<expectedOpcode/>` subconfiguration with the given parameters.

```k
    rule [foundry.call.expectStaticCall]:
         <k> #call_foundry SELECTOR ARGS
          => #loadAccount #asWord(#range(ARGS, 0, 32))
          ~> #setExpectOpcode #asWord(#range(ARGS, 0, 32)) #range(ARGS, 96, #asWord(#range(ARGS, 64, 32))) 0 Static
          ...
         </k>
      requires SELECTOR ==Int selector ( "expectStaticCall(address,bytes)" )

    rule [foundry.call.expectDelegateCall]:
         <k> #call_foundry SELECTOR ARGS
          => #loadAccount #asWord(#range(ARGS, 0, 32))
          ~> #setExpectOpcode #asWord(#range(ARGS, 0, 32)) #range(ARGS, 96, #asWord(#range(ARGS, 64, 32))) 0 Delegate
          ...
         </k>
      requires SELECTOR ==Int selector ( "expectDelegateCall(address,bytes)" )

    rule [foundry.call.expectRegularCall]:
         <k> #call_foundry SELECTOR ARGS
          => #loadAccount #asWord(#range(ARGS, 0, 32))
          ~> #setExpectOpcode #asWord(#range(ARGS, 0, 32)) #range(ARGS, 128, #asWord(#range(ARGS, 96, 32))) #asWord(#range(ARGS, 32, 32)) Call
          ...
         </k>
      requires SELECTOR ==Int selector ( "expectRegularCall(address,uint256,bytes)" )

    rule [foundry.call.expectCreate]:
         <k> #call_foundry SELECTOR ARGS
          => #loadAccount #asWord(#range(ARGS, 0, 32))
          ~> #setExpectOpcode #asWord(#range(ARGS, 0, 32)) #range(ARGS, 128, #asWord(#range(ARGS, 96, 32))) #asWord(#range(ARGS, 32, 32)) Create
          ...
         </k>
      requires SELECTOR ==Int selector ( "expectCreate(address,uint256,bytes)" )

    rule [foundry.call.expectCreate2]:
         <k> #call_foundry SELECTOR ARGS
          => #loadAccount #asWord(#range(ARGS, 0, 32))
          ~> #setExpectOpcode #asWord(#range(ARGS, 0, 32)) #range(ARGS, 128, #asWord(#range(ARGS, 96, 32))) #asWord(#range(ARGS, 32, 32)) Create2
          ...
         </k>
      requires SELECTOR ==Int selector ( "expectCreate2(address,uint256,bytes)" )
```

Next, everytime one of the `STATICCALL`, `DELEGATECALL`, `CALL`, `CREATE` or `CREATE2` opcodes is executed, we check if the `sender` address, `msg.value` and `calldata` match the expected values.
`calldata` needs to match only the first byte.

```k
    rule <k> (. => #clearExpectOpcode) ~> STATICCALL _GCAP ACCTTO ARGSTART ARGWIDTH _RETSTART _RETWIDTH ... </k>
         <localMem> LM </localMem>
         <expectedOpcode>
           <isOpcodeExpected> true </isOpcodeExpected>
           <expectedAddress> ACCTTO </expectedAddress>
           <expectedData> DATA </expectedData>
           <opcodeType> Static </opcodeType>
           ...
         </expectedOpcode>
      requires #range(LM, ARGSTART, ARGWIDTH) ==K #range(DATA, 0, ARGWIDTH)
      [priority(40)]

    rule <k> (. => #clearExpectOpcode) ~> DELEGATECALL _GCAP ACCTTO ARGSTART ARGWIDTH _RETSTART _RETWIDTH ... </k>
         <localMem> LM </localMem>
         <expectedOpcode>
           <isOpcodeExpected> true </isOpcodeExpected>
           <expectedAddress> ACCTTO </expectedAddress>
           <expectedData> DATA </expectedData>
           <opcodeType> Delegate </opcodeType>
           ...
         </expectedOpcode>
      requires #range(LM, ARGSTART, ARGWIDTH) ==K #range(DATA, 0, ARGWIDTH)
      [priority(40)]

    rule <k> (. => #clearExpectOpcode) ~> CALL _GCAP ACCTTO VALUE ARGSTART ARGWIDTH _RETSTART _RETWIDTH ... </k>
         <localMem> LM </localMem>
         <expectedOpcode>
           <isOpcodeExpected> true </isOpcodeExpected>
           <expectedAddress> ACCTTO </expectedAddress>
           <expectedData> DATA </expectedData>
           <opcodeType> Call </opcodeType>
           <expectedValue> VALUE </expectedValue>
         </expectedOpcode>
      requires #range(LM, ARGSTART, ARGWIDTH) ==K #range(DATA, 0, ARGWIDTH)
      [priority(40)]

    rule <k> (. => #clearExpectOpcode) ~> CREATE VALUE MEMSTART MEMWIDTH ... </k>
         <localMem> LM </localMem>
         <id> ACCT </id>
         <expectedOpcode>
           <isOpcodeExpected> true </isOpcodeExpected>
           <expectedAddress> ACCT </expectedAddress>
           <expectedData> DATA </expectedData>
           <opcodeType> Create </opcodeType>
           <expectedValue> VALUE </expectedValue>
         </expectedOpcode>
      requires #range(LM, MEMSTART, MEMWIDTH) ==K #range(DATA, 0, MEMWIDTH)
      [priority(40)]

    rule <k> (. => #clearExpectOpcode) ~> CREATE2 VALUE MEMSTART MEMWIDTH _SALT ... </k>
         <localMem> LM </localMem>
         <id> ACCT </id>
         <expectedOpcode>
           <isOpcodeExpected> true </isOpcodeExpected>
           <expectedAddress> ACCT </expectedAddress>
           <expectedData> DATA </expectedData>
           <opcodeType> Create2 </opcodeType>
           <expectedValue> VALUE </expectedValue>
         </expectedOpcode>
      requires #range(LM, MEMSTART, MEMWIDTH) ==K #range(DATA, 0, MEMWIDTH)
      [priority(40)]
```

Pranks
------

#### Injecting addresses in a call

To inject the pranked `msg.sender` and `tx.origin` we add two new rules for the `#call` production, defined in [evm.md](./evm.md).
These rules have a higher priority.
The only difference between these rules is that one will also set the `tx.origin`, if required.
First, will match only if the `<active>` cell has the `true` value, signaling that a prank is active, and if the current depth of the call is at the same level with the depth at which the prank was invoked.
This is needed in order to prevent overwriting the caller for subcalls.
Finally, the original sender of the transaction, `ACCTFROM` is changed to the new caller, `NCL`.

```k
    rule [foundry.prank.injectCaller]:
         <k> #call (ACCTFROM => NCL) _ACCTTO _ACCTCODE _VALUE _APPVALUE _ARGS _STATIC ... </k>
         <callDepth> CD </callDepth>
         <prank>
            <newCaller> NCL </newCaller>
            <newOrigin> .Account </newOrigin>
            <active> true </active>
            <depth> CD </depth>
            ...
         </prank>
      requires NCL =/=K .Account
       andBool ACCTFROM =/=Int NCL
      [priority(40)]

    rule [foundry.prank.injectCallerAndOrigin]:
         <k> #call (ACCTFROM => NCL) _ACCTTO _ACCTCODE _VALUE _APPVALUE _ARGS _STATIC ... </k>
         <callDepth> CD </callDepth>
         <origin> _ => NOG </origin>
         <prank>
            <newCaller> NCL </newCaller>
            <newOrigin> NOG </newOrigin>
            <active> true </active>
            <depth> CD </depth>
            ...
         </prank>
      requires NCL =/=K .Account
       andBool NOG =/=K .Account
       andBool ACCTFROM =/=Int NCL
      [priority(40)]
```

We define a new rule for the `#halt ~> #return _ _` production that will trigger the `#endPrank` rules if the prank was set only for a single call and if the current call depth is equal to the depth at which `prank` was invoked plus one.


```k
    rule <k> (. => #endPrank) ~> #halt ~> #return _RETSTART _RETWIDTH ... </k>
         <callDepth> CD </callDepth>
         <prank>
           <singleCall> true </singleCall>
           <depth> PD </depth>
           ...
         </prank>
      requires CD ==Int PD +Int 1
      [priority(40)]
```

#### `startPrank` - Sets `msg.sender` and `tx.origin` for all subsequent calls until `stopPrank` is called.

```
function startPrank(address) external;
function startPrank(address sender, address origin) external;
```

`foundry.call.startPrank` and `foundry.call.startPrankWithOrigin` will match when either of `startPrank` functions are called.
The addresses which will be used to impersonate future calls are retrieved from the local memory using `#asWord(#range(ARGS, 0, 32)` for the sender, and `#asWord(#range(ARGS, 32, 32)` for the origin (only for the `foundry.call.startPrankWithOrigin` rule).
The `#loadAccount` production is used to load accounts into the state if they are missing.

```k
    rule [foundry.call.startPrank]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(ARGS) ~> #setPrank #asWord(ARGS) .Account false ... </k>
      requires SELECTOR ==Int selector ( "startPrank(address)" )

    rule [foundry.call.startPrankWithOrigin]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(#range(ARGS, 0, 32)) ~> #loadAccount #asWord(#range(ARGS, 32, 32)) ~> #setPrank #asWord(#range(ARGS, 0, 32)) #asWord(#range(ARGS, 32, 32)) false ... </k>
      requires SELECTOR ==Int selector ( "startPrank(address,address)" )
```

#### `prank` - Impersonate `msg.sender` and `tx.origin` for only for the next call.

```
function prank(address) external;
function prank(address sender, address origin) external;
```

```k
    rule [foundry.call.prank]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(ARGS) ~> #setPrank #asWord(ARGS) .Account true ... </k>
      requires SELECTOR ==Int selector ( "prank(address)" )

    rule [foundry.call.prankWithOrigin]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(#range(ARGS, 0, 32)) ~> #loadAccount #asWord(#range(ARGS, 32, 32)) ~> #setPrank #asWord(#range(ARGS, 0, 32)) #asWord(#range(ARGS, 32, 32)) true ... </k>
      requires SELECTOR ==Int selector ( "prank(address,address)" )
```

#### `stopPrank` - Stops impersonating `msg.sender` and `tx.origin`.

```
function stopPrank() external;
```

`foundry.call.stopPrank` will match when `stopPrank` function will be called. This rule will invoke `#endPrank` which will clean up the `<prank/>` subconfiguration and restore the previous values of the `msg.sender` and `tx.origin`.

```k
    rule [foundry.call.stopPrank]:
         <k> #call_foundry SELECTOR _ => #endPrank ... </k>
      requires SELECTOR ==Int selector ( "stopPrank()" )
```

Gas Manipulation
----------------

```
function infiniteGas() external;
```

Set the remaining gas to an infinite value.
This is useful for running tests without them running out of gas.

```{.k .bytes .symbolic}
    rule [foundry.call.infiniteGas]:
         <k> #call_foundry SELECTOR _ARGS => . ... </k>
         <gas> _ => #gas(?_VGAS) </gas>
         <callGas> _ => #gas(?_VCALLGAS) </callGas>
      requires SELECTOR ==Int selector ( "infiniteGas()" )
```

Expecting Events
----------------
```
function expectEmit(bool checkTopic1, bool checkTopic2, bool checkTopic3, bool checkData) external;
function expectEmit(bool checkTopic1, bool checkTopic2, bool checkTopic3, bool checkData, address emitter) external;
```

Assert a specific log is emitted before the end of the current function.

Call the cheat code, specifying whether we should check the first, second or third topic, and the log data.
Topic 0 is always checked.
Emit the event we are supposed to see before the end of the current function.
Perform the call.
If the event is not available in the current scope (e.g. if we are using an interface, or an external smart contract), we can define the event ourselves with an identical event signature.

There are 2 signatures:

Without checking the emitter address: Asserts the topics match without checking the emitting address.
With address: Asserts the topics match and that the emitting address matches.

```k
    rule [foundry.call.expectEmit]:
         <k> #call_foundry SELECTOR ARGS => #setExpectEmit word2Bool(#asWord(#range(ARGS, 0, 32))) word2Bool(#asWord(#range(ARGS, 32, 32))) word2Bool(#asWord(#range(ARGS, 64, 32))) word2Bool(#asWord(#range(ARGS, 96, 32))) .Account ... </k>
      requires SELECTOR ==Int selector ( "expectEmit(bool,bool,bool,bool)" )

    rule [foundry.call.expectEmitAddr]:
         <k> #call_foundry SELECTOR ARGS => #setExpectEmit word2Bool(#asWord(#range(ARGS, 0, 32))) word2Bool(#asWord(#range(ARGS, 32, 32))) word2Bool(#asWord(#range(ARGS, 64, 32))) word2Bool(#asWord(#range(ARGS, 96, 32))) #asWord(#range(ARGS, 128, 32)) ... </k>
      requires SELECTOR ==Int selector ( "expectEmit(bool,bool,bool,bool,address)" )
```

```k
    rule <k> LOG(N) _MEMSTART _MEMWIDTH ... </k>
         <expectEmit>
          <recordEvent> true => false </recordEvent>
          <isEventExpected> false => true </isEventExpected>
          ...
        </expectEmit>
        <wordStack> WS </wordStack>
      requires #sizeWordStack(WS) >=Int N
      [priority(40)]

    rule <k> (. => #clearExpectEmit) ~> LOG(N) MEMSTART MEMWIDTH ... </k>
         <log> _ ListItem({ _ | TOPICS | DATA }:SubstateLogEntry) </log>
         <expectEmit>
          <recordEvent> false </recordEvent>
          <isEventExpected> true </isEventExpected>
          <checkedTopics> CHECKS </checkedTopics>
          <checkedData> CHECKDATA </checkedData>
          <expectedEventAddress> .Account </expectedEventAddress>
        </expectEmit>
        <wordStack> WS </wordStack>
        <localMem> LM </localMem>
      requires #sizeWordStack(WS) >=Int N
       andBool  #checkTopics(CHECKS, TOPICS, WordStack2List(#take(N, WS)))
       andBool ((notBool CHECKDATA) orBool (#asWord(DATA) ==Int #asWord(#range(LM, MEMSTART, MEMWIDTH))))
      [priority(40)]

    rule <k> (. => #clearExpectEmit) ~> LOG(N) MEMSTART MEMWIDTH ... </k>
         <log> _ ListItem({ _ | TOPICS | DATA }:SubstateLogEntry) </log>
         <id> ACCT </id>
         <expectEmit>
          <recordEvent> false </recordEvent>
          <isEventExpected> true </isEventExpected>
          <checkedTopics> CHECKS </checkedTopics>
          <checkedData> CHECKDATA </checkedData>
          <expectedEventAddress> ACCT </expectedEventAddress>
        </expectEmit>
        <wordStack> WS </wordStack>
        <localMem> LM </localMem>
      requires #sizeWordStack(WS) >=Int N
       andBool  #checkTopics(CHECKS, TOPICS, WordStack2List(#take(N, WS)))
       andBool ((notBool CHECKDATA) orBool (#asWord(DATA) ==Int #asWord(#range(LM, MEMSTART, MEMWIDTH))))
      [priority(40)]
```


Restricting the accounts that can be called in KEVM
---------------------------------------------------

A `StorageSlot` pair is formed from an address and a storage index.

```k
    syntax StorageSlot ::= "{" Int "|" Int "}"
 // ------------------------------------------
```

The `ACCTTO` value is checked for each call while the whitelist restriction is enabled for calls.
If the address is not in the whitelist `WLIST` then `KEVM` goes into an error state providing the `ACCTTO` value.

```k
    rule [foundry.catchNonWhitelistedCalls]:
         <k> (#call _ ACCTTO _ _ _ _ false
          ~> #popCallStack
          ~> #popWorldState) => #end FOUNDRY_WHITELISTCALL ... </k>
         <whitelist>
           <isCallWhitelistActive> true </isCallWhitelistActive>
           <addressSet> WLIST </addressSet>
           ...
         </whitelist>
      requires notBool ACCTTO in WLIST
      [priority(40)]
```

When the storage whitelist restriction is enabled, the `SSTORE` operation will check if the address and the storage index are in the whitelist.
If the pair is not present in the whitelist `WLIST` then `KEVM` goes into an error state providing the address and the storage index values.

```k
    rule [foundry.catchNonWhitelistedStorageChanges]:
         <k> SSTORE INDEX _ => #end FOUNDRY_WHITELISTSTORAGE ... </k>
         <id> ACCT </id>
         <statusCode> _ => FOUNDRY_WHITELISTSTORAGE </statusCode>
         <whitelist>
           <isStorageWhitelistActive> true </isStorageWhitelistActive>
           <storageSlotSet> WLIST </storageSlotSet>
           ...
         </whitelist>
      requires notBool {ACCT|INDEX} in WLIST
      [priority(40)]
```

#### `allowCallsToAddress` - Add an account address to a whitelist.

```
function allowCallsToAddress(address) external;
```

Adds an account address to the whitelist. The execution of the modified KEVM will stop when a call has been made to an address which is not in the whitelist.

```k
    rule [foundry.allowCallsToAddress]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(ARGS) ~> #addAddressToWhitelist #asWord(ARGS) ... </k>
         requires SELECTOR ==Int selector ( "allowCallsToAddress(address)" )
```

#### `allowChangesToStorage` - Add an account address and a storage slot to a whitelist.

```
function allowChangesToStorage(address,uint256) external;
```

```k
    rule [foundry.allowStorageSlotToAddress]:
         <k> #call_foundry SELECTOR ARGS => #loadAccount #asWord(ARGS) ~> #addStorageSlotToWhitelist { #asWord(#range(ARGS, 0, 32)) | #asWord(#range(ARGS, 32, 32)) } ... </k>
         requires SELECTOR ==Int selector ( "allowChangesToStorage(address,uint256)" )
```


#### `sign` - Signs a digest with private key

```
function sign(uint256 privateKey, bytes32 digest) external returns (uint8 v, bytes32 r, bytes32 s);
```

`foundry.call.sign` will match when the `sign` cheat code function is called.
This rule then takes from the `privateKey` to sign using `#range(ARGS,0,32)` and the `digest` to be signed using `#range(ARGS, 32, 32)`.
To perform the signature we use the `ECDSASign ( String, String )` function (from KEVM).
This function receives as arguments 2 strings: the data to be signed and the private key, therefore we use `#unparseByteStack` to convert the `Bytes` with the `privateKey` and `digest` into strings.
The `ECDSASign` function returns the signed data in [r,s,v] form, which we convert to a `Bytes` using `#parseByteStack`.

```k
    rule [foundry.call.sign]:
         <k> #call_foundry SELECTOR ARGS => . ... </k>
         <output> _ => #sign(#range(ARGS, 32, 32),#range(ARGS,0,32)) </output>
      requires SELECTOR ==Int selector ( "sign(uint256,bytes32)" )
```

Otherwise, throw an error for any other call to the Foundry contract.

```k
    rule [foundry.call.owise]:
         <k> #call_foundry SELECTOR ARGS => #error_foundry SELECTOR ARGS ... </k>
         <statusCode> _ => FOUNDRY_UNIMPLEMENTED </statusCode>
      [owise]
```

Utils
-----

- `#loadAccount ACCT` creates a new, empty account for `ACCT` if it does not already exist. Otherwise, it has no effect.

```k
    syntax KItem ::= "#loadAccount" Int [klabel(foundry_loadAccount)]
 // -----------------------------------------------------------------
    rule <k> #loadAccount ACCT => #accessAccounts ACCT ... </k> <account> <acctID> ACCT </acctID> ... </account>
    rule <k> #loadAccount ACCT => #newAccount ACCT ~> #accessAccounts ACCT ... </k> [owise]
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
    syntax KItem ::= "#setCode" Int Bytes [klabel(foundry_setCode)]
 // ---------------------------------------------------------------
    rule <k> #setCode ACCTID CODE => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <code> _ => #if #asWord(CODE) ==Int 0 #then .Bytes #else CODE #fi </code>
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

`#setSymbolicStorage ACCTID` takes a given account and makes its storage fully symbolic.

```k
     syntax KItem ::= "#setSymbolicStorage" Int [klabel(foundry_setSymbolicStorage)]
```

```{.k .symbolic}
    rule <k> #setSymbolicStorage ACCTID => . ... </k>
         <account>
           <acctID> ACCTID </acctID>
           <storage> _ => ?STORAGE </storage>
           <origStorage> _ => ?STORAGE </origStorage>
           ...
         </account>
```

- `#setExpectRevert` sets the `<expectedRevert>` subconfiguration with the current call depth and the expected message from `expectRevert`.

```k
    syntax KItem ::= "#setExpectRevert" Bytes [klabel(foundry_setExpectRevert)]
 // ---------------------------------------------------------------------------
    rule <k> #setExpectRevert EXPECTED => . ... </k>
         <callDepth> CD </callDepth>
         <expectedRevert>
           <isRevertExpected> false => true </isRevertExpected>
           <expectedDepth> _ => CD +Int 1 </expectedDepth>
           <expectedReason> _ => EXPECTED </expectedReason>
         </expectedRevert>
```

- `#clearExpectRevert` sets the `<expectedRevert>` subconfiguration to initial values.

```k
    syntax KItem ::= "#clearExpectRevert" [klabel(foundry_clearExpectRevert)]
 // -------------------------------------------------------------------------
    rule <k> #clearExpectRevert => . ... </k>
         <output> _ => #buf (512, 0) </output>
         <expectedRevert>
           <isRevertExpected> _ => false </isRevertExpected>
           <expectedDepth> _ => 0 </expectedDepth>
           <expectedReason> _ => .Bytes </expectedReason>
         </expectedRevert>
```

- `#encodeOutput` - will encode the output `Bytes` to match the encoding of the `Bytes` in `<expectedReason>` cell.
    - If the `revert` instruction  and the `expectRevert` cheat code are used with with a custom error, then `expectRevert` will store the message with the encoding `abi.encode(abi.encodeWithSelector(CustomError.selector, 1, 2))`, while the output cell will contain only the `abi.encodeWithSelector(CustomError.selector, 1, 2)`.
    - If the `revert` instruction  and the `expectRevert` cheat code are used with with a string, then `expectRevert` will store the only the encoded string, while the `<output>` cell will store the encoded built-in error `Error(string)`.
    Since the encoding `abi.encode(abi.encodeWithSelector(CustomError.selector, 1, 2))` cannot be easily decoded when symbolic variables are used, the `<output>` Bytes is encoded again when the default `Error(string)` is not used.

```k
    syntax Bytes ::= "#encodeOutput" "(" Bytes ")" [function, total, klabel(foundry_encodeOutput)]
 // ----------------------------------------------------------------------------------------------
    rule #encodeOutput(BA) => #abiCallData("expectRevert", #bytes(BA)) requires notBool #range(BA, 0, 4) ==K Int2Bytes(4, selector("Error(string)"), BE)
    rule #encodeOutput(BA) => BA [owise]
```

- `#checkRevertReason` will compare the contents of the `<output>` cell with the `Bytes` from `<expectReason>`.

```k
    syntax KItem ::= "#checkRevertReason" [klabel(foundry_checkRevertReason)]
 // -------------------------------------------------------------------------
    rule <k> #checkRevertReason => . ... </k>
         <statusCode> _ => EVMC_SUCCESS </statusCode>
         <output> OUT </output>
         <expectedRevert>
           <expectedReason> REASON </expectedReason>
           ...
         </expectedRevert>
      requires #matchReason(REASON, #encodeOutput(OUT))

    rule <k> #checkRevertReason => #markAsFailed ... </k>
         <output> OUT </output>
         <expectedRevert>
           <expectedReason> REASON </expectedReason>
           ...
         </expectedRevert>
      requires notBool #matchReason(REASON, #encodeOutput(OUT))
```

- `#matchReason(REASON,OUT)` will check if the returned message matches the expected reason of the revert.
Will also return true if REASON is `.Bytes`.

```k
    syntax Bool ::= "#matchReason" "(" Bytes "," Bytes ")" [function, klabel(foundry_matchReason)]
 // ----------------------------------------------------------------------------------------------
    rule #matchReason(REASON, _) => true requires REASON ==K .Bytes
    rule #matchReason(REASON, OUT) => REASON ==K #range(OUT, 4, lengthBytes(OUT) -Int 4) requires REASON =/=K .Bytes
```

- `#setExpectOpcode` initializes the `<expectedOpcode>` subconfiguration with an expected `Address`, and `Bytes` to match the calldata.
`CallType` is used to specify what `CALL*` opcode is expected.

```k
    syntax KItem ::= "#setExpectOpcode" Account Bytes Int OpcodeType [klabel(foundry_setExpectOpcode)]
 // --------------------------------------------------------------------------------------------------
    rule <k> #setExpectOpcode ACCT DATA VALUE OPTYPE => . ... </k>
         <expectedOpcode>
           <isOpcodeExpected> _ => true </isOpcodeExpected>
           <expectedAddress> _ => ACCT </expectedAddress>
           <expectedData> _ => DATA </expectedData>
           <expectedValue> _ => VALUE </expectedValue>
           <opcodeType> _ => OPTYPE </opcodeType>
         </expectedOpcode>
```

- `#clearExpectOpcode` restore the `<expectedOpcode>` subconfiguration to its initial values.

```k
    syntax KItem ::= "#clearExpectOpcode" [klabel(foundry_clearExpectOpcode)]
 // -------------------------------------------------------------------------
    rule <k> #clearExpectOpcode => . ... </k>
         <expectedOpcode>
           <isOpcodeExpected> _ => false </isOpcodeExpected>
           <expectedAddress> _ => .Account </expectedAddress>
           <expectedData> _ => .Bytes </expectedData>
           <opcodeType> _ => .OpcodeType </opcodeType>
           <expectedValue> _ => 0 </expectedValue>
         </expectedOpcode>
```

- `#setPrank NEWCALLER NEWORIGIN SINGLEPRANK` will set the `<prank/>` subconfiguration for the given accounts.

```k
    syntax KItem ::= "#setPrank" Int Account Bool [klabel(foundry_setPrank)]
 // ------------------------------------------------------------------------
    rule <k> #setPrank NEWCALLER NEWORIGIN SINGLEPRANK => . ... </k>
         <callDepth> CD </callDepth>
         <caller> CL </caller>
         <origin> OG </origin>
         <prank>
           <prevCaller> .Account => CL </prevCaller>
           <prevOrigin> .Account => OG </prevOrigin>
           <newCaller> _ => NEWCALLER </newCaller>
           <newOrigin> _ => NEWORIGIN </newOrigin>
           <active> false => true </active>
           <depth> _ => CD </depth>
           <singleCall> _ => SINGLEPRANK </singleCall>
         </prank>
```

- `#endPrank` will end the prank, restoring the previous caller and origin to the `<caller>` and `<origin>` cells in the configuration.
If the production is matched when no prank is active, it will be ignored.

```k
    syntax KItem ::= "#endPrank" [klabel(foundry_endPrank)]
 // -------------------------------------------------------
    rule <k> #endPrank => #clearPrank ... </k>
        <caller> _ => CL </caller>
        <origin> _ => OG </origin>
        <prank>
          <prevCaller> CL </prevCaller>
          <prevOrigin> OG </prevOrigin>
          <active> true </active>
          ...
        </prank>

    rule <k> #endPrank => . ... </k>
        <prank>
          <active> false </active>
          ...
        </prank>
```

- `#clearPrank` will clear the prank subconfiguration.

```k
    syntax KItem ::= "#clearPrank" [klabel(foundry_clearPrank)]
 // -----------------------------------------------------------
    rule <k> #clearPrank => . ... </k>
        <prank>
          <prevCaller> _ => .Account </prevCaller>
          <prevOrigin> _ => .Account </prevOrigin>
          <newCaller> _ => .Account </newCaller>
          <newOrigin> _ => .Account </newOrigin>
          <active> _ => false </active>
          <depth> _ => 0 </depth>
          <singleCall> _ => false </singleCall>
        </prank>
```
```k
    syntax Bytes ::= #sign ( Bytes , Bytes ) [function,klabel(foundry_sign)]
 // ------------------------------------------------------------------------
    rule #sign(BA1, BA2) => #parseByteStack(ECDSASign(#unparseByteStack(BA1), #unparseByteStack(BA2))) [concrete]
```

- `#setExpectEmit` will initialize the `<expectEmit/>` subconfiguration, based on the arguments provided with the `expectEmit` cheat code.

```k
    syntax KItem ::= "#setExpectEmit" Bool Bool Bool Bool Account [klabel(foundry_setExpectEmit)]
 // ---------------------------------------------------------------------------------------------
    rule <k> #setExpectEmit T1 T2 T3 CHECKDATA ACCT => . ... </k>
         <expectEmit>
           <recordEvent> _ => true </recordEvent>
           <isEventExpected> _ => false </isEventExpected>
           <checkedTopics> _ => ListItem(true) ListItem(T1) ListItem(T2) ListItem(T3) .List </checkedTopics>
           <checkedData> _ => CHECKDATA </checkedData>
           <expectedEventAddress> _ => ACCT </expectedEventAddress>
         </expectEmit>
```

- `#clearExpectEmit` is used to clear the `<expectEmit/>` subconfiguration and restore initial values.

```k
    syntax KItem ::= "#clearExpectEmit" [klabel(foundry_clearExpectEmit)]
 // ---------------------------------------------------------------------
    rule <k> #clearExpectEmit => . ...</k>
         <expectEmit>
           <recordEvent> _ => false </recordEvent>
           <isEventExpected> _ => false </isEventExpected>
           <checkedTopics> _ => .List </checkedTopics>
           <checkedData> _ => false </checkedData>
           <expectedEventAddress> _ => .Account </expectedEventAddress>
         </expectEmit>
```

- `#checkTopics` and `#checkTopic` are functions that compare the `TOPICS` of the expected `Event` with those of the currently emitted `Event`.

```k
    syntax Bool ::= "#checkTopic" "(" Bool "," Int "," Int ")" [function, klabel(foundry_checkTopic)]
                  | "#checkTopics" "(" List "," List "," List ")" [function, klabel(foundry_checkTopics)]
 // -----------------------------------------------------------------------------------------------------
    rule #checkTopic(CHECK, V1, V2) => (notBool CHECK) orBool (V1 ==Int V2)

    rule #checkTopics(.List, _, _) => true
    rule #checkTopics(ListItem(true), L1, L2) => false requires L1 ==K .List orBool L2 ==K .List
    rule #checkTopics(ListItem(false), L1, L2) => true requires L1 ==K .List orBool L2 ==K .List
    rule #checkTopics(ListItem(CHECK) CHECKS, ListItem(V1) L1, ListItem(V2) L2) => #checkTopic(CHECK, V1, V2) andBool #checkTopics(CHECKS, L1, L2)
```

- `#addAddressToWhitelist` enables the whitelist restriction for calls and adds an address to the whitelist.

```k
    syntax KItem ::= "#addAddressToWhitelist" Int [klabel(foundry_addAddressToWhitelist)]
 // -------------------------------------------------------------------------------------
    rule <k> #addAddressToWhitelist ACCT => . ... </k>
        <whitelist>
          <isCallWhitelistActive> _ => true </isCallWhitelistActive>
          <addressSet>  WLIST => WLIST SetItem(ACCT) </addressSet>
          ...
        </whitelist>
```

- `#addStorageSlotToWhitelist` enables the whitelist restriction for storage chagnes and adds a `StorageSlot` item to the whitelist.

```k
    syntax KItem ::= "#addStorageSlotToWhitelist" StorageSlot [klabel(foundry_addStorageSlotToWhitelist)]
 // -----------------------------------------------------------------------------------------------------
    rule <k> #addStorageSlotToWhitelist SLOT => . ... </k>
        <whitelist>
          <isStorageWhitelistActive> _ => true </isStorageWhitelistActive>
          <storageSlotSet> WLIST => WLIST SetItem(SLOT) </storageSlotSet>
          ...
        </whitelist>
```

- selectors for cheat code functions.

```k
    rule ( selector ( "assume(bool)" )                             => 1281615202 )
    rule ( selector ( "deal(address,uint256)" )                    => 3364511341 )
    rule ( selector ( "etch(address,bytes)" )                      => 3033974658 )
    rule ( selector ( "warp(uint256)" )                            => 3856056066 )
    rule ( selector ( "roll(uint256)" )                            => 528174896  )
    rule ( selector ( "fee(uint256)" )                             => 968063664  )
    rule ( selector ( "chainId(uint256)" )                         => 1078582738 )
    rule ( selector ( "coinbase(address)" )                        => 4282924116 )
    rule ( selector ( "label(address,string)" )                    => 3327641368 )
    rule ( selector ( "getNonce(address)" )                        => 755185067  )
    rule ( selector ( "addr(uint256)" )                            => 4288775753 )
    rule ( selector ( "load(address,bytes32)" )                    => 1719639408 )
    rule ( selector ( "store(address,bytes32,bytes32)" )           => 1892290747 )
    rule ( selector ( "setNonce(address,uint64)" )                 => 4175530839 )
    rule ( selector ( "expectRevert()" )                           => 4102309908 )
    rule ( selector ( "expectRevert(bytes)" )                      => 4069379763 )
    rule ( selector ( "startPrank(address)" )                      => 105151830  )
    rule ( selector ( "startPrank(address,address)" )              => 1169514616 )
    rule ( selector ( "stopPrank()" )                              => 2428830011 )
    rule ( selector ( "expectStaticCall(address,bytes)" )          => 2232945516 )
    rule ( selector ( "expectDelegateCall(address,bytes)" )        => 1030406631 )
    rule ( selector ( "expectRegularCall(address,uint256,bytes)" ) => 1973496647 )
    rule ( selector ( "expectCreate(address,uint256,bytes)" )      => 658968394  )
    rule ( selector ( "expectCreate2(address,uint256,bytes)" )     => 3854582462 )
    rule ( selector ( "expectEmit(bool,bool,bool,bool)" )          => 1226622914 )
    rule ( selector ( "expectEmit(bool,bool,bool,bool,address)" )  => 2176505587 )
    rule ( selector ( "sign(uint256,bytes32)" )                    => 3812747940 )
    rule ( selector ( "symbolicStorage(address)" )                 => 769677742  )
    rule ( selector ( "freshUInt(uint8)" )                         => 625253732  )
    rule ( selector ( "freshBool()" )                              => 2935720297 )
    rule ( selector ( "prank(address)" )                           => 3395723175 )
    rule ( selector ( "prank(address,address)" )                   => 1206193358 )
    rule ( selector ( "allowCallsToAddress(address)" )             => 1850795572 )
    rule ( selector ( "allowChangesToStorage(address,uint256)" )   => 4207417100 )
    rule ( selector ( "infiniteGas()" )                            => 3986649939 )
```

- selectors for unimplemented cheat code functions.

```k
    rule selector ( "expectRegularCall(address,bytes)" )        => 3178868520
    rule selector ( "expectNoCall()" )                          => 3861374088
    rule selector ( "ffi(string[])" )                           => 2299921511
    rule selector ( "setEnv(string,string)" )                   => 1029252078
    rule selector ( "envBool(string)" )                         => 2127686781
    rule selector ( "envUint(string)" )                         => 3247934751
    rule selector ( "envInt(string)" )                          => 2301234273
    rule selector ( "envAddress(string)" )                      => 890066623
    rule selector ( "envBytes32(string)" )                      => 2543095874
    rule selector ( "envString(string)" )                       => 4168600345
    rule selector ( "envBytes(string)" )                        => 1299951366
    rule selector ( "envBool(string,string)" )                  => 2863521455
    rule selector ( "envUint(string,string)" )                  => 4091461785
    rule selector ( "envInt(string,string)" )                   => 1108873552
    rule selector ( "envAddress(string,string)" )               => 2905717242
    rule selector ( "envBytes32(string,string)" )               => 1525821889
    rule selector ( "envString(string,string)" )                => 347089865
    rule selector ( "envBytes(string,string)" )                 => 3720504603
    rule selector ( "expectRevert(bytes4)" )                    => 3273568480
    rule selector ( "record()" )                                => 644673801
    rule selector ( "accesses(address)" )                       => 1706857601
    rule selector ( "mockCall(address,bytes calldata,bytes)" )  => 378193464
    rule selector ( "mockCall(address,uint256,bytes,bytes)" )   => 2168494993
    rule selector ( "clearMockedCalls()" )                      => 1071599125
    rule selector ( "expectCall(address,bytes)" )               => 3177903156
    rule selector ( "expectCall(address,uint256,bytes)" )       => 4077681571
    rule selector ( "getCode(string)" )                         => 2367473957
    rule selector ( "broadcast()" )                             => 2949218368
    rule selector ( "broadcast(address)" )                      => 3868601563
    rule selector ( "startBroadcast()" )                        => 2142579071
    rule selector ( "startBroadcast(address)" )                 => 2146183821
    rule selector ( "stopBroadcast()" )                         => 1995103542
    rule selector ( "readFile(string)" )                        => 1626979089
    rule selector ( "readLine(string)" )                        => 1895126824
    rule selector ( "writeFile(string,string)" )                => 2306738839
    rule selector ( "writeLine(string,string)" )                => 1637714303
    rule selector ( "closeFile(string)" )                       => 1220748319
    rule selector ( "removeFile(string)" )                      => 4054835277
    rule selector ( "toString(address)" )                       => 1456103998
    rule selector ( "toString(bytes)" )                         => 1907020045
    rule selector ( "toString(bytes32)" )                       => 2971277800
    rule selector ( "toString(bool)" )                          => 1910302682
    rule selector ( "toString(uint256)" )                       => 1761649582
    rule selector ( "toString(int256)" )                        => 2736964622
    rule selector ( "recordLogs()" )                            => 1101999954
    rule selector ( "getRecordedLogs()" )                       => 420828068
    rule selector ( "snapshot()" )                              => 2534502746
    rule selector ( "revertTo(uint256)" )                       => 1155002532
    rule selector ( "createFork(string,uint256)" )              => 1805892139
    rule selector ( "createFork(string)" )                      => 834286744
    rule selector ( "createSelectFork(string,uint256)" )        => 1911440973
    rule selector ( "createSelectFork(string)" )                => 2556952628
    rule selector ( "selectFork(uint256)" )                     => 2663344167
    rule selector ( "activeFork()" )                            => 789593890
    rule selector ( "rollFork(uint256)" )                       => 3652973473
    rule selector ( "rollFork(uint256,uint256)" )               => 3612115876
    rule selector ( "rpcUrl(string)" )                          => 2539285737
    rule selector ( "rpcUrls()" )                               => 2824504344
    rule selector ( "deriveKey(string,uint32)" )                => 1646872971
```

- selector for Solidity built-in Error

```k
    rule ( selector ( "Error(string)" ) => 147028384 )
```
```k
endmodule
```
