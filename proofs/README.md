EVM Program Verification
========================

The EVM program verifier combines the K verification infrastructure with the EVM semantics.
We present a brief summary of our verification efforts.

The SUM To N Program
--------------------

As a demonstration of simple reachability claims involing a circularity, we prove the EVM sum program correct.
This program sums the numbers from 1 to N (for sufficiently small N), including pre-conditions dis-allowing integer under/overflow and stack overflow.
The specification [Sum to N](sum-to-n.md) is given as reachability rules using the K syntax.

[The ERC20 Token Standard](https://github.com/ethereum/EIPs/issues/20)
----------------------------------------------------------------------

The ERC20 standard is a specification that describes several simple methods that a smart contract must implement in order to be treated as a token by a variety of higher level applications (including wallets, exchanges, and other contracts expecting to interact with tokens).
The implementation details of these methods are left to the user, with minimal semantic behavior provided in the specification, leaving room for a wide range of complex tokens (and the associated security vulnerabilities).
The ERC20 standard requires the following Solidity methods and events (and log items) to be implemented:

```js
// Get the total token supply
    function totalSupply() constant returns (uint256 totalSupply)

// Get the account balance of another account with address _owner
    function balanceOf(address _owner) constant returns (uint256 balance)

// Send _value amount of tokens to address _to
    function transfer(address _to, uint256 _value) returns (bool success)

// Send _value amount of tokens from address _from to address _to
    function transferFrom(address _from, address _to, uint256 _value) returns (bool success)

// Allow _spender to withdraw from your account, multiple times, up to the _value amount.
// If this function is called again it overwrites the current allowance with _value.
    function approve(address _spender, uint256 _value) returns (bool success)

// Returns the amount which _spender is still allowed to withdraw from _owner
    function allowance(address _owner, address _spender) constant returns (uint256 remaining)

// Triggered when tokens are transferred.
    event Transfer(address indexed _from, address indexed _to, uint256 _value)

// Triggered whenever approve(address _spender, uint256 _value) is called.
    event Approval(address indexed _owner, address indexed _spender, uint256 _value)
```

Here we'll collect the list of ERC20 tokens we have analyzed.
The following files contain details about each token and the proof claims we have verified.

-   [HKG Hacker Gold Token](hkg.md)

Running Proofs
==============

The verification part is compatible with uiuck.
Proofs generated from these markdown files will be placed in `tests/proofs/...`.
Using the `./Build` script, you can compile the definition and run the proofs.
See `./Build help` for more information about compiling and running programs/proofs.

Note that:

1.  It may take a long time (probably more than half an hour) to verify the `transfer` and `transferFrom` function of token program.
2.  The verification of `token-buggy-spec.k` is not able to go through.
