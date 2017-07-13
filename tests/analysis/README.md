The K ecosystem provides a full-fleged program verifier that we use to prove properties about smart contracts.
We present a brief summary of our verification efforts.

The Hacker Gold (HKG) Token Smart Contract
------------------------------------------

The HKG token is an ERC-20 compliant token smart contract written in solidity.
The token became a [topic of discussion](https://www.ethnews.com/ethercamps-hkg-token-has-a-bug-and-needs-to-be-reissued)
when a subtle vulnerability lead to a reissue. The token had been originally
audited by Zeppelin, and was deemed secure.

## Using K's verifier on the HKG Token

### Compiling Solidity Source To EVM

Since we don't currently have a complete semantics of
Solidity in K, we had to first compile the [HKG Token's Source](https://github.com/ether-camp/virtual-accelerator/blob/master/contracts/StandardToken.sol)
to EVM. To simplify the verification process, we fixed the the total supply, added two dummy accounts before compiling the code to EVM.
```javascript
contract StandardToken is TokenInterface {
```
...
```javascript
function StandardToken() {
    totalSupply = 5000;

    balances[dummy1] = 2000;
    balances[dummy2] = 3000;

    allowed[dummy1][dummy2] = balances[dummy1];
    allowed[dummy2][dummy1] = balances[dummy2];
}

```
Here's what the `transfer_from` function looks, pasted verbatim from HKG Token's source file
```javascript
 /**
     * transferFrom() - used to move allowed funds from other owner
     *                  account
     *
     *  @param from  - move funds from account
     *  @param to    - move funds to account
     *  @param value - move the value
     *
     *  @return - return true on success false otherwise
     */
    function transferFrom(address from, address to, uint256 value) returns (bool success) {

        if ( balances[from] >= value &&
             allowed[from][msg.sender] >= value &&
             value > 0) {


            // do the actual transfer
            balances[from] -= value;
            balances[to] += value;


            // addjust the permision, after part of
            // permited to spend value was used
            allowed[from][msg.sender] -= value;

            // rise the Transfer event
            Transfer(from, to, value);
            return true;
        } else {

            return false;
        }
    }
}
```

### Our Proof Claims

The K prover takes as input `Reachability claims`. The claims
are written exactly like `rules` in the semantics. The claims
have to be supplied to K via a `specification` file. Since our
HKG token contract contains only sequential code (no loops), our
specification file contains a single claim which looks like -

```
    rule
        ...
        <ethereum>
            <evm>
                <txExecState>
                    <program>   //Compiled Solidity Code                       </program>
                    ...
                    // Symbolic Value TRANSFER represents the amount to be used in as argument to the transfer_from method
                    <wordStack> TRANSFER:Int : REMAINING_STACK => ?W:WordStack </wordStack>
                    ...
                    // In the Ethereum ABI conforming compiled code, the transfer_from function starts from program counter 818.
                    <pc>        818   => 1331                                  </pc>
                </txExecState>
                ...
            </evm>
            <network>
                ...
                <accounts>
                    <account>
                        ...
                        <code>  //Compiled Solidity Code </code>
                        // We omit actual Values Here for the sake of readability
                        // Notice
                        <storage>... (TOTAL_SUPPLY |-> 5000) (DUMMY_ACCOUNT_1_BALANCE |-> (2000 => 2000 -Int TRANSFER)) ...
                            (DUMMY_ACCOUNT_2_BALANCE |-> (3000 => 3000 +Int TRANSFER)) </storage>
                        <acctMap> "nonce" |-> 0 </acctMap>
                    </account>
                </accounts>
                <messages> .Bag </messages>
            </network>
        </ethereum>
        requires TRANSFER >Int 0 andBool TRANSFER <Int 2000
```

The rule above specifies the property that all possible valid executions of the `transfer_from` function, must end
in a state where a symbolic amount `TRANSFER` is deducted from Dummy Account 1 and added to Dummy Account 2.


### The Results
The K prover was able to prove the all path reachability rule without fuss. We then looked at Token's history,
and realized that the vulnerability had been [fixed](https://github.com/ether-camp/virtual-accelerator/commit/78920651dff0ac0e13101e17842e54f73ee46633)

We then took the buggy code, compiled it to EVM, and plugged in into our reachabilty rule.
We then fed the claim to our prover, and it couldn't prove the claim. We're working towards
improving the error message that K throws while attempting to prove the claim so that
the messages themselves indicate the source of the bug.

We went one step further, and tried to prove the `transfer` function's correctness. The reachability claim
for the `transfer` function looks very similar, and we attempt to prove the same thing - all valid executions
of the function must end in a state where the amount is deducted from the message sender's balance, and added to
reciever's balance. The proof went through without any fuss for both the correct and buggy versions of the contract.

### Moral Of The Story
We were able to catch the bug in Hacker Gold's ERC-20 compliant token using our semantics. What stood out to the
team was the fact that the bug was caught using a very naive proof claim - something that possibly the authors of the
contract and the auditors at Zepellin could've easily come up with had our semantics been available then.
