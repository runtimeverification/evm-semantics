EVM Program Verification
========================

The EVM program verifier combines the K verification infrastructure with the EVM semantics.
We present a brief summary of our verification efforts.

The SUM To N Program
--------------------

As a demonstration of simple reachability claims involing a circularity, we prove the EVM sum program correct.
This program sums the numbers from 1 to N (for sufficiently small N), including pre-conditions dis-allowing integer under/overflow and stack overflow.
The specification [Sum to N](sum-to-n.md) is given as reachability rules using the K syntax.

The Hacker Gold (HKG) Token Smart Contract
------------------------------------------

The HKG token is an implementation of the ERC20 specification written in Solidity.
The token became a [topic of discussion](https://www.ethnews.com/ethercamps-hkg-token-has-a-bug-and-needs-to-be-reissued) when a subtle vulnerability lead to a reissue.
The token had been originally audited by [Zeppelin](https://zeppelin.solutions/security-audits), and was deemed secure.

### Compiling Solidity Source To EVM

Since we are performing our verification at the EVM level, the first step in the verification process is to compile the [HKG Token's Source](https://github.com/ether-camp/virtual-accelerator/blob/master/contracts/StandardToken.sol) to EVM.
To simplify the verification process, we fixed the total supply, and added two dummy accounts before compiling the code to EVM.

```solidity
contract StandardToken is TokenInterface {
//...
function StandardToken() {
    totalSupply = 5000;

    balances[dummy1] = 2000;
    balances[dummy2] = 3000;

    allowed[dummy1][dummy2] = balances[dummy1];
    allowed[dummy2][dummy1] = balances[dummy2];
}
```

Here's what the `transferFrom` function looks like, pasted verbatim from HKG Token's source file.

```solidity
  /*
   * transferFrom() - used to move allowed funds from other owner account
   *                  account
   *
   *  @param from  - move funds from account
   *  @param to    - move funds to account
   *  @param value - move the value
   *
   *  @return - return true on success false otherwise
   */
    function transferFrom(address from, address to, uint256 value)
     returns (bool success) {

        if ( balances[from] >= value &&
             allowed[from][msg.sender] >= value &&
             value > 0) {

            // do the transfer
            balances[from] -= value;
            balances[to]   += value;

            // addjust senders allowed spending
            allowed[from][msg.sender] -= value;

            // raise a Transfer
            Transfer(from, to, value);

            // success!
            return true;

        } else {
            return false;
        }
    }
}
```

This function is specified in the ERC20 standard described previously as "Send `_value` amount of tokens from address `_from` to address `_to`", and requires the `_from` address to approve the transfer of at least the amount being sent using ERC20's approve functionality.

### Our Proof Claims

The K prover takes as input *Reachability claims*.
The claims are written in the same format as rules from a language definition.
Since our HKG token contract contains only sequential code (without loops), each specification in our [specification file](hkg.md) contains a single claim for each branch.
The claims have to be supplied to K via a specification file (ends in `-spec.k`).

The following claim captures the behavior of the `transferFrom` function.

```k
    rule <k>       #execute ... </k>
         <id>      %ACCT_ID     </id>
         <program> %HKG_Program </program>

         <pc>  818 => 1331         </pc>
         <gas> G   => G -Int 16071 </gas>

         <wordStack>                        TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
                  => A1 -Int TRANSFER : 0 : TRANSFER : %CALLER_ID : %ORIGIN_ID : WS
         </wordStack>

         <account>
           <acctID>  %ACCT_ID               </acctID>
           <code>    %function_transferFrom </code>
           <storage> %ACCT_1_BALANCE |-> (B1 => B1 -Int TRANSFER)
                     %ACCT_1_ALLOWED |-> (A1 => A1 -Int TRANSFER)
                     %ACCT_2_BALANCE |-> (B2 => B2 +Int TRANSFER)
                     %ACCT_2_ALLOWED |-> _
                     ...
           </storage>
           ...
         </account>
         ...
      requires TRANSFER >Int 0
       andBool B1 >=Int TRANSFER andBool B1               <Int pow256
       andBool B2 >=Int 0        andBool B2 +Int TRANSFER <Int pow256
       andBool A1 >=Int TRANSFER andBool A1               <Int pow256
       andBool #sizeWordStack(WS) <Int 1016
       andBool G >=Int 16071
```

The rule above specifies that in all valid executions starting in the left-hand-side of the rule, either execution will never terminate or it will reach an instance of the right-hand-side.

-   Any symbol starting with a `%` indicates a constant which has been replaced by a symbol for clarity.
    In particular, `%HKG_Program` is the EVM bytecode for the `Hacker Gold` token program.
-   The program counter starts at 818 and ends at 1331, which are the start and end of the `transferFrom` function in the compiled EVM.
-   `TRANSFER` represents the symbolic amonut to transfer, `B1` and `B2` are the starting balances of accounts 1 and 2, repsectively, and `A1` is the allowance of account 1.
-   The terms in the `<storage>` cell capture the behavior of `transferFrom` function, which means that any transfer of amount `TRANSFER` from account 1 to account 2 (with `TRANSFER` sufficiently low and various overflow conditions met) will happen as intended in the execution of the `transferFrom` code provided.
-   The program counter starts at 818 and ends at 1331, which are the start and end of the `transferFrom` function in the compiled EVM.
-   The require clause states the following preconditions:

    a.  the condition that the `then` branch of the function meets;
    b.  the balance of each account should be low enough to avoid overflow during the transaction;
    c.  bounds the size of `WS` to ensure there is no stack overflow in runtime; and
    d.  there is enough gas for the execution of this fuction.

### The Results

The K prover was able to prove all the five functions implemented in `HKG` token program, where the code cell was initialized with the correct compiled HKG token code.
We then looked at Token's history, and realized that the vulnerability had been [fixed](https://github.com/ether-camp/virtual-accelerator/commit/78920651dff0ac0e13101e17842e54f73ee46633).

We then took the vulnerability containing code, compiled it to EVM, and plugged in into our [reachability claim](token-buggy-spec.md).
We then fed the claim to our prover, and it couldn't prove the claim.
We're working towards improving the error message that K throws while attempting to prove the claim so that the messages themselves indicate the source of the bug.

### Conclusion

With our semantics, we were able to not only catch the bug in Hacker Gold's ERC-20 compliant token using our semantics, but also find two overflow issues may occur in `HKG` token program, which could be missed by manual inspection and testing.
What stood out to the team was the fact that a full verification has a capability of finding subtle cases in interactions between the contract and its underlying execution platform.

### TODO

Right now we are proving complete specifications for each of the functions of the HKG token program, i.e., covering all the cases that the code covers.
To achieve a full verification, we need to analyze the cases when gas is not enough for the transaction and arithmetic overflow occurs at runtime.

Install K
=========

The verification part is compatible with the verification verison of K.

```sh
$ git clone https://github.com/kframework/k.git
$ mvn clean
$ mvn package -DskipTests
```

### Kompile the definition

```sh
$ ./Build
```

### Run the Prover

```sh
$ krun -d .build/uiuck --prove tests/proofs/*-spec.k proofs/json/*.json -cMODE=NORMAL -cSCHEDULE=DEFAULT
```

Note:

1.  It may take a long time (probably more than half an hour) to verify the transfer and transfer-From function of token program.
2.  The verification of "token-buggy-spec.k" is not able to go through.
