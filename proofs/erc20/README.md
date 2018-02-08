Formal Verification of ERC20 Smart Contracts
============================================

We present full functional correctness verification of ERC20 token contracts, for the first time to the best of our knowledge.
First, we formalize its high-level business logic, called [ERC20-K](https://github.com/runtimeverification/erc20-semantics), based on the [ERC20 standard](https://github.com/ethereum/EIPs/blob/master/EIPS/eip-20.md) document, to provide a precise and comprehensive specification of the functional correctness properties.
Then, we refine the specification down to EVM level to capture EVM-specific detailed behaviors, ensuring nothing bad happens in the actual execution, other than specified in the high-level specification.
To precisely reason about the EVM bytecodes without missing any EVM quirks, we adopted [KEVM](https://github.com/kframework/evm-semantics), a complete formal semantics of EVM, and instantiated the [K-framework's reachability logic theorem prover](http://fsl.cs.illinois.edu/index.php/Semantics-Based_Program_Verifiers_for_All_Languages) to generate a correct-by-construct deductive verifier for EVM.
We optimized the verifier by introducing custom abstractions and lemmas specific to EVM that expedite proof search of the underlying theorem prover.
We used the verifier to verify multiple ERC20 token contracts against the EVM-level specification, and found diverging behaviors of which some are questionable.
We believe that the techniques we developed here can be also readily used for verifying other smart contracts.

Artifact and Documentation
--------------------------

 * [ERC20-K](https://github.com/runtimeverification/erc20-semantics): a formal specification of the high-level business logic of ERC20
 * [ERC20-EVM](.): an EVM-level refinement of ERC20-K
   * [tmpl.k](tmpl.k): specification template
   * [viper/](viper): Viper ERC20 token specification
   * [zeppelin/](zeppelin): OpenZeppelin ERC20 token specification
   * [hkg/](hkg): HackerGold (HKG) ERC20 token specification
   * [hobby/](hobby): specification for an ERC20 token of a personal hobby, called KidsEducationToken
 * [Technical Report](tech-report.pdf): full details of the verification

ERC20 Token Contracts
---------------------

We tried to verify the following ERC20 token contract implementations against [ERC20-K](https://github.com/runtimeverification/erc20-semantics) and its refinement [ERC20-EVM](.), and found deviations as follows: 

 * [Viper ERC20 token](https://github.com/ethereum/vyper/blob/master/examples/tokens/ERC20_solidity_compatible/ERC20.v.py): fully *conforming* to the ERC20 standard
 * [OpenZeppelin ERC20 token](https://github.com/OpenZeppelin/zeppelin-solidity/blob/master/contracts/token/ERC20/StandardToken.sol): *conforming* to the standard, but:
   * Rejecting transfers to address `0`
 * [ConsenSys ERC20 token](https://github.com/ConsenSys/Tokens/blob/master/contracts/eip20/EIP20.sol): *conforming* to the standard, but:
   * No arithmetic overflow protection
   * Supporting infinite allowances variant
 * [HackerGold (HKG) ERC20 token](https://github.com/ether-camp/virtual-accelerator/blob/master/contracts/StandardToken.sol): *deviating* from the standard:
   * No arithmetic overflow protection
   * No `totalSupply` function
   * Rejecting transfers of `0` values
   * Returning `false` in failure
 * An ERC20 token of a personal hobby, called [KidsEducationToken](https://github.com/ethereum/mist/issues/3301): *buggy* implementation:
   * Typographical bug: `<=` instead of `>=`
   * Incorrect overflow detection for self-transfers
   * Rejecting transfers of `0` values
   * Returning `false` in failure


TODO: instruction for running proofs.
