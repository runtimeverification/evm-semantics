The K ecosystem provides a full-fledged program verifier that we use to prove properties about smart contracts.
We present a brief summary of our verification efforts.

The Hacker Gold (HKG) Token Smart Contract
------------------------------------------

The HKG token is an ERC-20 compliant token smart contract written in solidity.
The token became a [topic of discussion](https://www.ethnews.com/ethercamps-hkg-token-has-a-bug-and-needs-to-be-reissued) when a subtle vulnerability lead to a reissue.
The token had been originally audited by [Zeppelin](https://zeppelin.solutions/security-audits), and was deemed secure.

### Compiling Solidity Source To EVM

Since we currently don't have a complete semantics of Solidity in K, we had to first compile the [HKG Token's Source](https://github.com/ether-camp/virtual-accelerator/blob/master/contracts/StandardToken.sol) to EVM.
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
   * transferFrom() - used to move allowed funds from other owner
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

### Our Proof Claims

The K prover takes as input *Reachability claims*.
The claims are written exactly like *rules* in the semantics.
The claims have to be supplied to K via a specification file (ends in `-spec.k`).
Since our HKG token contract contains only sequential code (no loops), our [specification file](token-correct-transfer-from-spec.md) contains a single claim for each branch.

Here is a (very abbreviated) sample reachability claim for the `transferFrom` function.
We omit actual values here for readability.

```k
    rule ...
         <ethereum>
           <evm>
             <txExecState>
               <program> //Compiled Solidity Code </program>

               // Symbolic Value TRANSFER represents the amount to be used
               // in as argument to the transferFrom method
               <wordStack> TRANSFER:Int : REMAINING_STACK => ?W:WordStack </wordStack>

               // In the Ethereum ABI conforming compiled code,
               // the transferFrom function starts from program counter 818.
               <pc>        818   => 1331                                  </pc>
             </txExecState>
             ...
           </evm>
           <network>
             ...
             <accounts>
               <account>
                 <code> //Compiled Solidity Code </code>
                 <storage> ...
                           (TOTAL_SUPPLY            |-> TOTAL)
                           (DUMMY_ACCOUNT_1_BALANCE |-> (B1 => ?B1 -Int TRANSFER))
                           (DUMMY_ACCOUNT_1_ALLOWED |-> (B1 => ?B1 -Int TRANSFER))
                           (DUMMY_ACCOUNT_2_BALANCE |-> (B2 => ?B2 +Int TRANSFER))
                 </storage>
                 ...
               </account>
             </accounts>
             ...
           </network>
         </ethereum>
         requires TRANSFER >Int 0 andBool TRANSFER <Int 2000
```

The rule above specifies the property that all valid executions of the `transferFrom` function must end in a state where a symbolic amount `TRANSFER` is deducted from Dummy Account 1 and added to Dummy Account 2.

### The Results

The K prover was able to prove the above mentioned all path reachability rule, where the code cell was initialized with the correct compiled HKG token code.
We then looked at Token's history, and realized that the vulnerability had been [fixed](https://github.com/ether-camp/virtual-accelerator/commit/78920651dff0ac0e13101e17842e54f73ee46633).

We then took the vulnerability containing code, compiled it to EVM, and plugged in into our [reachability claim](token-buggy-spec.md).
We then fed the claim to our prover, and it couldn't prove the claim.
We're working towards improving the error message that K throws while attempting to prove the claim so that the messages themselves indicate the source of the bug.

We went one step further, and tried to prove the `transfer` function's correctness.
The [reachability claim](token-correct-transfer-spec.md) for the `transfer` function looks very similar, and we attempt to prove the same thing - all valid executions of the function must end in a state where the amount is deducted from the message sender's balance, and added to receiver's balance.
The prover was able to verify the correctness of the token's `transfer` function's implementation as well.

### Conclusion

We were able to catch the bug in Hacker Gold's ERC-20 compliant token using our semantics.
What stood out to the team was the fact that the bug was caught using a very naive proof claim - something that possibly the authors of the contract and the auditors at Zeppelin could've easily come up with had our semantics been available then.

### TODO

Right now we are proving complete specifications for each of the functions of the HKG token program, that is, covering all the cases that the code covers.
To achieve a full verification, we need to analyze the cases when gas is not enough for the transaction and arithmetic overflow occurs at runtime.

Install K
=========

The verification part is compatible with the verification verison of K.

```sh
$ git clone https://github.com/kframework/k.git
$ mvn clean
$ mvn package -DskipTests
```

### Run the Prover

```sh
$ krun -d .build\uiuck --prove \proofs\*-spec.k \proofs\json\*.json -cMODE=NORMAL -cSCHEDULE=DEFAULT --z3-executable
```

Note:

1.  It may take a long time (probably more than half an hour) to verify the transfer and transfer-From function of token program.
2.  The verification of "token-buggy-spec.k" is not able to go through.
