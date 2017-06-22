// EVM Execution
// =============

// The EVM is a stack machine over some simple opcodes. Most of the opcodes are
// "local" to the execution state of the machine, but some of them must interact
// with the world state. This file only defines the local execution operations, the
// file `ethereum.md` will define the interactions with the world state.

// Configuration
// -------------

// The configuration has cells for the current account id, the current opcode, the
// program counter, the current gas, the gas price, the current program, the word
// stack, and the local memory. In addition, there are cells for the callstack and
// execution substate.

// We've broken up the configuration into two components; those parts of the state
// that mutate during execution of a single transaction and those that are static
// throughout. In the comments next to each cell, we've marked which component of
// the yellowpaper state corresponds to each cell.


requires "data.k"

module ETHEREUM
    imports EVM-DATA
    imports KCELLS

    configuration <ethereum>

                    // EVM Specific
                    // ============

                    <evm>

                      // Mutable during a single transaction
                      // -----------------------------------

                      <op>         .K          </op>
                      <output>     .WordStack  </output>                     // H_RETURN
                      <memoryUsed> 0:Word      </memoryUsed>                 // \mu_i
                      <callStack>  .CallStack  </callStack>
                      <callLog>    .CallLog    </callLog>

                      <txExecState>
                        <program> .Map </program>                       // I_b

                        // I_*
                        <id>        0:Word     </id>                    // I_a
                        <caller>    0:Word     </caller>                // I_s
                        <callData>  .WordStack </callData>              // I_d
                        <callValue> 0:Word     </callValue>             // I_v

                        // \mu_*
                        <wordStack> .WordStack </wordStack>             // \mu_s
                        <localMem>  .Map       </localMem>              // \mu_m
                        <pc>        0:Word     </pc>                    // \mu_pc
                        <gas>       0:Word     </gas>                   // \mu_g
                      </txExecState>

                      // A_* (execution substate)
                      <substate>
                        <selfDestruct> .Set         </selfDestruct>     // A_s
                        <log>          .SubstateLog </log>              // A_l
                        <refund>       0:Word       </refund>           // A_r
                      </substate>

                      // Immutable during a single transaction
                      // -------------------------------------

                      <gasPrice> 0:Word </gasPrice>                     // I_p
                      <origin>   0:Word </origin>                       // I_o

                      // I_H* (block information)
                      <gasLimit>   0:Word </gasLimit>                   // I_Hl
                      <coinbase>   0:Word </coinbase>                   // I_Hc
                      <timestamp>  0:Word </timestamp>                  // I_Hs
                      <number>     0:Word </number>                     // I_Hi
                      <difficulty> 0:Word </difficulty>                 // I_Hd

                    </evm>

                    // Ethereum Network
                    // ================

                    <network>

                      // Accounts Record
                      // ---------------

                      <activeAccounts> .Set </activeAccounts>

                      <accounts>
                        <account multiplicity="*">
                          <acctID>  .AcctID </acctID>
                          <balance> .Value  </balance>
                          <code>    .Code   </code>
                          <storage> .Map    </storage>
                          <acctMap> .Map    </acctMap>
                        </account>
                      </accounts>

                      // Transactions Record
                      // -------------------

                      <messages>
                        <message multiplicity="*">
                          <msgID>  .MsgID   </msgID>
                          <to>     .AcctID  </to>
                          <from>   .AcctID  </from>
                          <amount> .Value   </amount>
                          <data>   .Map     </data>
                        </message>
                      </messages>

                    </network>

                  </ethereum>

    syntax AcctID ::= Word | ".AcctID"
    syntax Code   ::= Map  | ".Code"
    syntax MsgID  ::= Word | ".MsgID"
    syntax Value  ::= Word | ".Value"


// Execution Cycle
// ---------------

// -   `#catch` is used to catch exceptional states so that the state can be
//     rolled back.
// -   `#exception` is used to indicate exceptional states.
// -   `#end` is used to indicate the (non-exceptional) end of execution.


    syntax KItem ::= "#catch" | "#exception" | "#end"
 // -------------------------------------------------
    rule <op> #exception ~> OP:OpCode => #exception ... </op>


// -   `#next` signals that it's time to begin the next execution cycle, which
//     means check if the next operator is exceptional then execute it if not.


    syntax InternalOp ::= "#next"
 // -----------------------------
    rule <op> #next => #exceptional?(OP) ~> #execOp(OP) ... </op>
         <pc> PCOUNT </pc>
         <program> ... PCOUNT |-> OP ... </program>

    rule <op> #next => #exception ... </op> <pc> PCOUNT </pc> <program> PGM </program>
      requires notBool PCOUNT in keys(PGM)


// Exception Checks
// ----------------

// In the yellowpaper the function `#exceptional?` is called `Z` (Section 9.4.2 in
// yellowpaper). It checks, in order:

// -   The instruction isn't `INVALID`.
// -   There are enough elements on the stack to supply the arguments.
// -   If it's a `JUMP*` operation, the destination is a valid `JUMPDEST`.
// -   Upon placing the results on the stack, there won't be a stack overflow.
// -   There is enough gas.


    syntax InternalOp ::= "#exceptional?" "(" OpCode ")"
 // ----------------------------------------------------
    rule <op> #exceptional?(OP)
           => #invalid?(OP)
           ~> #stackNeeded?(OP)
           ~> #stackAdded?(OP)
           ~> #badJumpDest?(OP)
           ~> #enoughGas?(OP)
          ...
         </op>
         <gas> GAVAIL </gas>
         <wordStack> WS </wordStack>


// ### Invalid Operator

// -   OpCode `INVALID` represents the designated invalid EVM operator.
// -   `#invalid?` checks if the given opcode is indeed `INVALID`.


    syntax InvalidOp ::= "INVALID"
 // ------------------------------

    syntax InternalOp ::= "#invalid?" "(" OpCode ")"
 // ------------------------------------------------
    rule <op> #invalid?(INVALID) => #exception ... </op>
    rule <op> #invalid?(OP)      => .          ... </op> requires notBool isInvalidOp(OP)


// ### Stack Size

// -   `#stackNeeded?` throws an exception if there are not enough arguments on
//     the stack.
// -   `#stackAdded?` throws an exception if there will be too many items on the
//     stack after the opcode completes.


    syntax InternalOp ::= "#stackNeeded?" "(" OpCode ")"
                        | "#stackAdded?" "(" OpCode ")"
 // ---------------------------------------------------
    rule <op> #stackNeeded?(OP) => #exception ... </op> <wordStack> WS </wordStack> requires #size(WS) <Int #stackNeeded(OP)
    rule <op> #stackNeeded?(OP) => .          ... </op> <wordStack> WS </wordStack> requires #size(WS) >=Int #stackNeeded(OP)

    rule <op> #stackAdded?(OP) => #exception ... </op> <wordStack> WS </wordStack> requires #size(WS) +Int #stackDelta(OP) >Int 1024
    rule <op> #stackAdded?(OP) => .          ... </op> <wordStack> WS </wordStack> requires #size(WS) +Int #stackDelta(OP) <=Int 1024


// -   `#stackNeeded` calculates how many arguments the operator needs from the
//     stack ($\delta$ in the yellowpaper).
// -   `#stackAdded` calculates how many words will be added to the stack by this
//     operator ($\alpha$ in the yellowpaper).
// -   `#stackDelta` calculates the difference in size of the stack after executing
//     the operator.


    syntax Int ::= #stackNeeded ( OpCode ) [function]
 // -------------------------------------------------
    rule #stackNeeded(NOP:NullStackOp) => 0
    rule #stackNeeded(UOP:UnStackOp)   => 1
    rule #stackNeeded(BOP:BinStackOp)  => 2
    rule #stackNeeded(TOP:TernStackOp) => 3
    rule #stackNeeded(QOP:QuadStackOp) => 4
    rule #stackNeeded(PUSH(_, _))      => 0
    rule #stackNeeded(DUP(N))          => N
    rule #stackNeeded(SWAP(N))         => N +Int 1
    rule #stackNeeded(LOG(N))          => N +Int 2
    rule #stackNeeded(DELEGATECALL)    => 6
    rule #stackNeeded(COP:CallOp)      => 7 requires COP =/=K DELEGATECALL

    syntax Int ::= #stackAdded ( OpCode ) [function]
 // ------------------------------------------------
    rule #stackAdded(OP)      => 0 requires OP in #zeroRet
    rule #stackAdded(DUP(N))  => N +Int 1
    rule #stackAdded(SWAP(N)) => N
    rule #stackAdded(OP)      => 1 requires notBool (OP in #zeroRet orBool isDupOp(OP) orBool isSwapOp(OP))

    syntax Int ::= #stackDelta ( OpCode ) [function]
 // ------------------------------------------------
    rule #stackDelta(OP) => #stackAdded(OP) -Int #stackNeeded(OP)

    syntax OpCodes ::= "#zeroRet"
 // -----------------------------
    rule #zeroRet =>   STOP ; CALLDATACOPY ; CODECOPY ; EXTCODECOPY ; POP
                     ; MSTORE ; MSTORE8 ; SSTORE ; JUMP ; JUMPI ; JUMPDEST
                     ; LOG(0) ; RETURN ; SELFDESTRUCT ; .OpCodes            [macro]


// ### Jump Destination

// -   `#badJumpDest?` checks that if it's a `JUMP*` operation that it's jumping to
//     a valid destination (Section 9.4.3 in yellowpaper).


    syntax InternalOp ::= "#badJumpDest?" "(" OpCode ")"
 // ----------------------------------------------------
    rule <op> #badJumpDest?(OP) => .          ... </op> requires OP =/=K JUMP andBool OP =/=K JUMPI
    rule <op> #badJumpDest?(OP) => .          ... </op> <wordStack> DEST : WS </wordStack> <program> ... DEST |-> JUMPDEST ... </program>
    rule <op> #badJumpDest?(OP) => #exception ... </op> <wordStack> DEST : WS </wordStack> <program> ... DEST |-> OP'      ... </program> requires (OP ==K JUMP orBool OP ==K JUMPI) andBool OP' =/=K JUMPDEST
    rule <op> #badJumpDest?(OP) => #exception ... </op> <wordStack> DEST : WS </wordStack> <program> PGM </program>                       requires (OP ==K JUMP orBool OP ==K JUMPI) andBool notBool DEST in keys(PGM)


// ### Gas Check

// -   `#enoughGas?` throws an exception if there isn't enough gas for the opcode.


    syntax InternalOp ::= "#enoughGas?" "(" OpCode ")" | "#checkGas"
 // ----------------------------------------------------------------
    rule <op> #enoughGas?(OP) => #gas(OP) ~> #checkGas ... </op>
    rule <op> G:Int ~> #checkGas => #exception ... </op> <gas> GAVAIL </gas> requires word2Bool(G >Word GAVAIL)
    rule <op> G:Int ~> #checkGas => .          ... </op> <gas> GAVAIL </gas> requires word2Bool(G <=Word GAVAIL)


// OpCode Execution
// ----------------

// Executing an opcode consists of deducting the necessary gas, calling it, then
// incrementing the program counter.


    syntax InternalOp ::= #execOp ( OpCode )
 // ----------------------------------------
    rule <op> #execOp(OP) => #gas(OP) ~> #deductGas ~> OP ~> #incrementPC(OP) ~> #next ... </op>


// ### Gas Deduction

// -   `#deductGas` removes the correct amount of gas from the current gas balance.


    syntax InternalOp ::= "#deductGas"
 // ----------------------------------
    rule <op> G:Int ~> #deductGas => . ... </op> <gas> GAVAIL => GAVAIL -Int G </gas>


// ### Argument Loading

// Depending on the sort of the opcode loaded, the correct number of arguments are
// loaded off the `wordStack`. This allows more "local" definition of each of the
// corresponding operators.


    syntax OpCode ::= NullStackOp | UnStackOp | BinStackOp | TernStackOp | QuadStackOp
                    | InvalidOp | StackOp | InternalOp | CallOp | PushOp | LogOp
 // ----------------------------------------------------------------------------

    syntax KItem ::= OpCode
                   | UnStackOp Word
                   | BinStackOp Word Word
                   | TernStackOp Word Word Word
                   | QuadStackOp Word Word Word Word
 // ------------------------------------------------
    rule <op> UOP:UnStackOp   => UOP W0          ... </op> <wordStack> W0 : WS                => WS </wordStack>
    rule <op> BOP:BinStackOp  => BOP W0 W1       ... </op> <wordStack> W0 : W1 : WS           => WS </wordStack>
    rule <op> TOP:TernStackOp => TOP W0 W1 W2    ... </op> <wordStack> W0 : W1 : W2 : WS      => WS </wordStack>
    rule <op> QOP:QuadStackOp => QOP W0 W1 W2 W3 ... </op> <wordStack> W0 : W1 : W2 : W3 : WS => WS </wordStack>

    syntax KItem ::= CallOp Word Word Word Word Word Word Word
                   | "DELEGATECALL" Word Word Word Word Word Word
 // -------------------------------------------------------------
    rule <op> DELEGATECALL => DELEGATECALL W0 W1 W2 W3 W4 W5    ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : WS      => WS </wordStack>
    rule <op> CO:CallOp    => CO           W0 W1 W2 W3 W4 W5 W6 ... </op> <wordStack> W0 : W1 : W2 : W3 : W4 : W5 : W6 : WS => WS </wordStack>
      requires CO =/=K DELEGATECALL

    syntax KItem ::= StackOp WordStack
 // ----------------------------------
    rule <op> SO:StackOp => SO WS ... </op> <wordStack> WS </wordStack>


// ### Increment Program Counter

// All operators except for `PUSH` increment the program counter by 1 (because the
// arguments to `PUSH` are inline).


    syntax InternalOp ::= #incrementPC ( OpCode ) 
 // ---------------------------------------------
    rule <op> #incrementPC(OP) => . ... </op> <pc> PCOUNT => PCOUNT +Word #pc(OP) </pc>

    syntax Word ::= #pc ( OpCode ) [function]
 // -----------------------------------------
    rule #pc(OP)         => 1 requires notBool isPushOp(OP)
    rule #pc(PUSH(N, _)) => 1 +Word N


// Other
// -----

// ### Substate Log

// During execution of a transaction some things are recorded in the substate log
// (Section 6.1 in yellowpaper). This is a right cons-list of `SubstateLogEntry`
// (which contains the account ID along with the specified portions of the
// `wordStack` and `localMem`).


    syntax SubstateLog      ::= ".SubstateLog" | SubstateLog "." SubstateLogEntry
    syntax SubstateLogEntry ::= "{" Word "|" WordStack "|" WordStack "}"


// After executing a transaction, it's necessary to have the effect of the substate
// log recorded.

// -   `#finalize` makes the substate log actually have an effect on the state.


    syntax InternalOp ::= "#finalize"
 // ---------------------------------
    rule <op> #finalize => . ... </op>
         <selfDestruct> .Set </selfDestruct>
         <refund>       0    </refund>

    rule <op> #finalize ... </op>
         <id> ACCT </id>
         <refund> BAL => 0 </refund>
         <account>
           <acctID> ACCT </acctID>
           <balance> CURRBAL => CURRBAL +Word BAL </balance>
           ...
         </account>
      requires BAL =/=K 0

    rule <op> #finalize ... </op>
         <selfDestruct> ... (SetItem(ACCT) => .Set) </selfDestruct>
         <activeAccounts> ... (SetItem(ACCT) => .Set) </activeAccounts>
         <accounts>
           ( <account>
               <acctID> ACCT </acctID>
               ...
             </account>
          => .Bag
           )
           ...
         </accounts>


// ### Memory Consumption

// Using memory while executing EVM costs gas, so the amount of memory used is
// tracked (Appendix H in yellowpaper).

// -   `#memoryUsageUpdate` is the function `M` in appendix H of the yellowpaper
//     which helps track the memory used.


    syntax Word ::= #memoryUsageUpdate ( Word , Word , Word ) [function]
 // --------------------------------------------------------------------
    rule #memoryUsageUpdate(S:Int, F:Int, 0)     => S
    rule #memoryUsageUpdate(S:Int, F:Int, L:Int) => maxWord(S, (F +Int L) up/Int 32)


// EVM Programs
// ============

// Lists of opcodes form programs. Deciding if an opcode is in a list will be
// useful for modeling gas, and converting a program into a map of program-counter
// to opcode is useful for execution.

// Note that `_in_` ignores the arguments to operators that are parametric.


    syntax OpCodes ::= ".OpCodes" | OpCode ";" OpCodes
 // --------------------------------------------------

    syntax Bool ::= OpCode "in" OpCodes [function]
 // ----------------------------------------------
    rule OP:OpCode  in .OpCodes            => false
    rule OP:OpCode  in (OP' ; OPS)         => (OP ==K OP') orElseBool (OP in OPS) requires notBool (isStackOp(OP) orBool isPushOp(OP) orBool isLogOp(OP))
    rule LOG(_)     in (LOG(_) ; OPS)      => true
    rule DUP(_)     in (DUP(_) ; OPS)      => true
    rule SWAP(_)    in (SWAP(_) ; OPS)     => true
    rule PUSH(_, _) in (PUSH(_, _) ; OPS)  => true

    syntax Map ::= #asMap ( OpCodes )       [function]
                 | #asMap ( Int , OpCodes ) [function]
 // --------------------------------------------------
    rule #asMap( OPS:OpCodes )         => #asMap(0, OPS)
    rule #asMap( N , .OpCodes )        => .Map
    rule #asMap( N , OP:OpCode ; OCS ) => (N |-> OP) #asMap(N +Int 1, OCS) requires notBool isPushOp(OP)
    rule #asMap( N , PUSH(M, W) ; OCS) => (N |-> PUSH(M, W)) #asMap(N +Int 1 +Int M, OCS)

    syntax OpCodes ::= #asOpCodes ( Map )       [function]
                     | #asOpCodes ( Int , Map ) [function]
 // ------------------------------------------------------
    rule #asOpCodes(M) => #asOpCodes(0, M)
    rule #asOpCodes(N, .Map) => .OpCodes
    rule #asOpCodes(N, N |-> OP         M) => OP         ; #asOpCodes(N +Int 1,        M) requires notBool isPushOp(OP)
    rule #asOpCodes(N, N |-> PUSH(S, W) M) => PUSH(S, W) ; #asOpCodes(N +Int 1 +Int S, M)

    syntax Word ::= #codeSize ( Map ) [function]
 // --------------------------------------------
    rule #codeSize(M) => #size(#asmOpCodes(#asOpCodes(M)))


// EVM OpCodes
// -----------

// Each subsection has a different class of opcodes. Organization is based roughly
// on what parts of the execution state are needed to compute the result of each
// operator. This sometimes corresponds to the organization in the yellowpaper.

// ### Internal Operations

// These are just used by the other operators for shuffling local execution state
// around on the EVM.

// -   `#push` will push an element to the `wordStack` without any checks.
// -   `#setStack_` will set the current stack to the given one.


    syntax InternalOp ::= "#push" | "#setStack" WordStack
 // -----------------------------------------------------
    rule <op> W0:Word ~> #push => . ... </op> <wordStack> WS => W0 : WS </wordStack>
    rule <op> #setStack WS     => . ... </op> <wordStack> _  => WS      </wordStack>


// Previous process states must be stored, so a tuple of sort `Process` is supplied
// for that. The `CallStack` is a cons-list of `Process`.

// -   `#pushCallStack` stores the current state on the `callStack`.
// -   `#popCallStack` replaces the current state with the top of the `callStack`.


    syntax CallStack ::= ".CallStack" | Bag CallStack
 // -------------------------------------------------

    syntax Int ::= #size ( CallStack ) [function]
 // ---------------------------------------------
    rule #size( .CallStack         ) => 0
    rule #size( B:Bag CS:CallStack ) => 1 +Int #size(CS)

    syntax InternalOp ::= "#pushCallStack" | "#popCallStack" | "#txFinished"
 // ------------------------------------------------------------------------
    rule <op> #pushCallStack => . ... </op>
         <callStack> CS => TXSTATE CS </callStack>
         <txExecState> TXSTATE </txExecState>

    rule <op> #popCallStack ~> #next => . ... </op>
         <callStack> TXSTATE CS => CS </callStack>
         <txExecState> _ => TXSTATE </txExecState>

    rule <op> #popCallStack ~> #next => #txFinished ... </op>
         <callStack> .CallStack </callStack>


// -   `#newAccount_` allows declaring a new empty account with the given address.


    syntax InternalOp ::= "#newAccount" Word
 // ----------------------------------------
    rule <op> #newAccount ACCT => . ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires #addr(ACCT) in ACCTS

    rule <op> #newAccount ACCT => . ... </op>
         <activeAccounts> ACCTS (.Set => SetItem(#addr(ACCT))) </activeAccounts>
         <accounts>
           ( .Bag
          => <account>
               <acctID>  #addr(ACCT)   </acctID>
               <balance> 0             </balance>
               <code>    .Map          </code>
               <storage> .Map          </storage>
               <acctMap> "nonce" |-> 0 </acctMap>
             </account>
           )
           ...
         </accounts>
      requires notBool #addr(ACCT) in ACCTS


// ### Stack Manipulations

// Some operators don't calculate anything, they just push the stack around a bit.


    syntax UnStackOp ::= "POP"
 // --------------------------
    rule <op> POP W => . ... </op>

    syntax StackOp ::= DUP ( Word ) | SWAP ( Word )
 // -----------------------------------------------
    rule <op> DUP(N)  WS:WordStack => #setStack ((WS [ N -Word 1 ]) : WS)                       ... </op>
    rule <op> SWAP(N) (W0 : WS)    => #setStack ((WS [ N -Word 1 ]) : (WS [ N -Word 1 := W0 ])) ... </op>

    syntax PushOp ::= PUSH ( Word , Word )
 // --------------------------------------
    rule <op> PUSH(_, W) => W ~> #push ... </op>


// ### Local Memory

// These operations are getters/setters of the local execution memory.


    syntax UnStackOp ::= "MLOAD"
 // ----------------------------
    rule <op> MLOAD INDEX => #asWord(#range(LM, INDEX, 32)) ~> #push ... </op>
         <localMem> LM </localMem>
         <memoryUsed> MU => maxInt(MU, (INDEX +Int 32) up/Int 32) </memoryUsed>

    syntax BinStackOp ::= "MSTORE" | "MSTORE8"
 // ------------------------------------------
    rule <op> MSTORE INDEX VALUE => . ... </op>
         <localMem> LM => LM [ INDEX := #padToWidth(32, #asByteStack(VALUE)) ] </localMem>
         <memoryUsed> MU => maxInt(MU, (INDEX +Int 32) up/Int 32) </memoryUsed>

    rule <op> MSTORE8 INDEX VALUE => . ... </op>
         <localMem> LM => LM [ INDEX <- (VALUE %Int 256) ]    </localMem>
         <memoryUsed> MU => maxInt(MU, (INDEX +Int 1) up/Int 32) </memoryUsed>


// ### Expressions

// Expression calculations are simple and don't require anything but the arguments
// from the `wordStack` to operate.

// NOTE: We have to call the opcode `OR` by `EVMOR` instead, because K has trouble
// parsing it/compiling the definition otherwise.


    syntax UnStackOp ::= "ISZERO" | "NOT"
 // -------------------------------------
    rule <op> ISZERO 0 => bool2Word(true)  ~> #push ... </op>
    rule <op> ISZERO W => bool2Word(false) ~> #push ... </op> requires W =/=K 0
    rule <op> NOT    W => ~Word W          ~> #push ... </op>

    syntax BinStackOp ::= "ADD" | "MUL" | "SUB" | "DIV" | "EXP" | "MOD"
 // -------------------------------------------------------------------
    rule <op> ADD W0 W1 => W0 +Word W1 ~> #push ... </op>
    rule <op> MUL W0 W1 => W0 *Word W1 ~> #push ... </op>
    rule <op> SUB W0 W1 => W0 -Word W1 ~> #push ... </op>
    rule <op> DIV W0 W1 => W0 /Word W1 ~> #push ... </op>
    rule <op> EXP W0 W1 => W0 ^Word W1 ~> #push ... </op>
    rule <op> MOD W0 W1 => W0 %Word W1 ~> #push ... </op>

    syntax BinStackOp ::= "SDIV" | "SMOD"
 // -------------------------------------
    rule <op> SDIV W0 W1 => W0 /sWord W1 ~> #push ... </op>
    rule <op> SMOD W0 W1 => W0 %sWord W1 ~> #push ... </op>

    syntax TernStackOp ::= "ADDMOD" | "MULMOD"
 // ------------------------------------------
    rule <op> ADDMOD W0 W1 W2 => (W0 +Int W1) %Word W2 ~> #push ... </op>
    rule <op> MULMOD W0 W1 W2 => (W0 *Int W1) %Word W2 ~> #push ... </op>

    syntax BinStackOp ::= "BYTE" | "SIGNEXTEND"
 // -------------------------------------------
    rule <op> BYTE INDEX W     => byte(INDEX, W)     ~> #push ... </op>
    rule <op> SIGNEXTEND W0 W1 => signextend(W0, W1) ~> #push ... </op>

    syntax BinStackOp ::= "AND" | "EVMOR" | "XOR"
 // ---------------------------------------------
    rule <op> AND   W0 W1 => W0 &Word W1   ~> #push ... </op>
    rule <op> EVMOR W0 W1 => W0 |Word W1   ~> #push ... </op>
    rule <op> XOR   W0 W1 => W0 xorWord W1 ~> #push ... </op>

    syntax BinStackOp ::= "LT" | "GT" | "EQ"
 // ----------------------------------------
    rule <op> LT W0 W1 => W0 <Word W1  ~> #push ... </op>
    rule <op> GT W0 W1 => W0 >Word W1  ~> #push ... </op>
    rule <op> EQ W0 W1 => W0 ==Word W1 ~> #push ... </op>

    syntax BinStackOp ::= "SLT" | "SGT"
 // -----------------------------------
    rule <op> SLT W0 W1 => W0 s<Word W1 ~> #push ... </op>
    rule <op> SGT W0 W1 => W1 s<Word W0 ~> #push ... </op>

    syntax BinStackOp ::= "SHA3"
 // ----------------------------
    rule <op> SHA3 MEMSTART MEMWIDTH => #parseHexWord(keccak(#byteStackToHex(#range(LM, MEMSTART, MEMWIDTH)))) ~> #push ... </op>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, MEMWIDTH) </memoryUsed>


// ### Local State

// These operators make queries about the current execution state.


    syntax NullStackOp ::= "PC" | "GAS" | "GASPRICE" | "GASLIMIT"
 // -------------------------------------------------------------
    rule <op> PC       => (PCOUNT -Int 1) ~> #push ... </op> <pc> PCOUNT </pc>
    rule <op> GAS      => GAVAIL          ~> #push ... </op> <gas> GAVAIL </gas>
    rule <op> GASPRICE => GPRICE          ~> #push ... </op> <gasPrice> GPRICE </gasPrice>
    rule <op> GASLIMIT => GLIMIT          ~> #push ... </op> <gasLimit> GLIMIT </gasLimit>

    syntax NullStackOp ::= "COINBASE" | "TIMESTAMP" | "NUMBER" | "DIFFICULTY"
 // -------------------------------------------------------------------------
    rule <op> COINBASE   => CB   ~> #push ... </op> <coinbase> CB </coinbase>
    rule <op> TIMESTAMP  => TS   ~> #push ... </op> <timestamp> TS </timestamp>
    rule <op> NUMBER     => NUMB ~> #push ... </op> <number> NUMB </number>
    rule <op> DIFFICULTY => DIFF ~> #push ... </op> <difficulty> DIFF </difficulty>

    syntax NullStackOp ::= "ADDRESS" | "ORIGIN" | "CALLER" | "CALLVALUE"
 // --------------------------------------------------------------------
    rule <op> ADDRESS   => ACCT ~> #push ... </op> <id> ACCT </id>
    rule <op> ORIGIN    => ORG  ~> #push ... </op> <origin> ORG </origin>
    rule <op> CALLER    => CL   ~> #push ... </op> <caller> CL </caller>
    rule <op> CALLVALUE => CV   ~> #push ... </op> <callValue> CV </callValue>

    syntax NullStackOp ::= "MSIZE" | "CODESIZE"
 // -------------------------------------------
    rule <op> MSIZE    => 32 *Word MU    ~> #push ... </op> <memoryUsed> MU </memoryUsed>
    rule <op> CODESIZE => #codeSize(PGM) ~> #push ... </op> <program> PGM </program>

    syntax TernStackOp ::= "CODECOPY"
 // ---------------------------------
    rule <op> CODECOPY MEMSTART PGMSTART WIDTH => . ... </op>
         <program> PGM </program>
         <localMem> LM => LM [ MEMSTART := #asmOpCodes(#asOpCodes(PGM)) [ PGMSTART .. WIDTH ] ] </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, WIDTH) </memoryUsed>

    syntax UnStackOp ::= "BLOCKHASH"
 // --------------------------------
    rule <op> BLOCKHASH N => #parseHexWord(keccak(#byteStackToHex(N : .WordStack))) ~> #push ... </op>


// ### `JUMP*`

// The `JUMP*` family of operations affect the current program counter.


    syntax NullStackOp ::= "JUMPDEST"
 // ------------------------------
    rule <op> JUMPDEST => . ... </op>

    syntax UnStackOp ::= "JUMP"
 // ---------------------------
    rule <op> JUMP DEST => . ... </op> <pc> _ => DEST </pc>

    syntax BinStackOp  ::= "JUMPI"
 // ------------------------------
    rule <op> JUMPI DEST I => . ... </op> <pc> _ => DEST </pc> requires I =/=K 0
    rule <op> JUMPI DEST 0 => . ... </op>


// ### `STOP` and `RETURN`


    syntax NullStackOp ::= "STOP"
 // -----------------------------
    rule <op> STOP => #end ... </op>

    syntax BinStackOp ::= "RETURN"
 // ------------------------------
    rule <op> RETURN RETSTART RETWIDTH => #end ... </op>
         <output> _ => #range(LM, RETSTART, RETWIDTH) </output>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, RETSTART, RETWIDTH) </memoryUsed>


// ### Call Data

// These operators query about the current `CALL*` state.


    syntax NullStackOp ::= "CALLDATASIZE"
 // -------------------------------------
    rule <op> CALLDATASIZE => #size(CD) ~> #push ... </op>
         <callData> CD </callData>

    syntax UnStackOp ::= "CALLDATALOAD"
 // -----------------------------------
    rule <op> CALLDATALOAD DATASTART => #asWord(CD [ DATASTART .. 32 ]) ~> #push ... </op>
         <callData> CD </callData>

    syntax TernStackOp ::= "CALLDATACOPY"
 // -------------------------------------
    rule <op> CALLDATACOPY MEMSTART DATASTART DATAWIDTH => . ... </op>
         <localMem> LM => LM [ MEMSTART := CD [ DATASTART .. DATAWIDTH ] ] </localMem>
         <callData> CD </callData>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, DATAWIDTH) </memoryUsed>


// ### Log Operations


    syntax LogOp ::= LOG ( Word )
 // -----------------------------
    rule <op> LOG(N) => . ... </op>
         <id> ACCT </id>
         <wordStack> W0 : W1 : WS => #drop(N, WS) </wordStack>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, W0, W1) </memoryUsed>
         <log> CURRLOG => CURRLOG . { ACCT | #take(N, WS) | #range(LM, W0, W1) } </log>
      requires word2Bool(#size(WS) >=Word N)


// Ethereum Network OpCodes
// ------------------------

// Operators that require access to the rest of the Ethereum network world-state
// can be taken as a first draft of a "blockchain generic" language.

// ### Account Queries

// TODO: It's unclear what to do in the case of an account not existing for these
// operators. `BALANCE` is specified to push 0 in this case, but the others are not
// specified. For now, I assume that they instantiate an empty account and use the
// empty data.


    syntax UnStackOp ::= "BALANCE"
 // ------------------------------
    rule <op> BALANCE ACCT => BAL ~> #push ... </op>
         <account>
           <acctID> ACCTACT </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires #addr(ACCT) ==K ACCTACT

    rule <op> BALANCE ACCT => #newAccount ACCT ~> 0 ~> #push ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addr(ACCT) in ACCTS

    syntax UnStackOp ::= "EXTCODESIZE"
 // ----------------------------------
    rule <op> EXTCODESIZE ACCTTO => #codeSize(CODE) ~> #push ... </op>
         <account>
           <acctID> ACCTTOACT </acctID>
           <code> CODE </code>
           ...
         </account>
      requires #addr(ACCTTO) ==K ACCTTOACT

    rule <op> EXTCODESIZE ACCTTO => #newAccount ACCTTO ~> 0 ~> #push ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addr(ACCTTO) in ACCTS

    syntax QuadStackOp ::= "EXTCODECOPY"
 // ------------------------------------
    rule <op> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => . ... </op>
         <localMem> LM => LM [ MEMSTART := #asmOpCodes(#asOpCodes(PGM)) [ PGMSTART .. WIDTH ] ] </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, WIDTH) </memoryUsed>
         <account>
           <acctID> ACCTACT </acctID>
           <code> PGM </code>
           ...
         </account>
      requires #addr(ACCT) ==K ACCTACT

    rule <op> EXTCODECOPY ACCT MEMSTART PGMSTART WIDTH => #newAccount ACCT ... </op>
         <activeAccounts> ACCTS </activeAccounts>
      requires notBool #addr(ACCT) in ACCTS


// ### Account Storage Operations

// These operations interact with the account storage.


    syntax UnStackOp ::= "SLOAD"
 // ----------------------------
    rule <op> SLOAD INDEX => 0 ~> #push ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account> requires notBool INDEX in keys(STORAGE)

    rule <op> SLOAD INDEX => VALUE ~> #push ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> ... INDEX |-> VALUE ... </storage>
           ...
         </account> 

    syntax BinStackOp ::= "SSTORE"
 // ------------------------------
    rule <op> SSTORE INDEX 0 => . ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> ... (INDEX |-> VALUE => .Map) ... </storage>
           ...
         </account>
         <refund> R => R +Word Rsclear </refund>

    rule <op> SSTORE INDEX 0 => . ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE </storage>
           ...
         </account>
      requires notBool (INDEX in keys(STORAGE))

    rule <op> SSTORE INDEX VALUE => . ... </op>
         <id> ACCT </id>
         <account>
           <acctID> ACCT </acctID>
           <storage> STORAGE => STORAGE [ INDEX <- VALUE ] </storage>
           ...
         </account>
      requires VALUE =/=K 0


// Call Operations
// ---------------

// The various `CALL*` (and other inter-contract control flow) operations will be
// desugared into these `InternalOp`s.

// -   `#returnLoc__` is a placeholder for the calling program, specifying where to
//     place the returned data in memory.


    syntax InternalOp ::= "#returnLoc" Word Word
 // --------------------------------------------
    rule <op> #returnLoc RETSTART RETWIDTH => . ... </op>
         <output> OUT </output>
         <localMem> LM => LM [ RETSTART := #take(minWord(RETWIDTH, #size(OUT)), OUT) ] </localMem>


// -   The `callLog` is used to store the `CALL*`/`CREATE` operations so that we
//     can compare them against the test-set.

// TODO: The `Call` sort needs to store the available gas to the `CALL*` as well,
// but we are not right now because gas calculation isn't finished.


    syntax Call ::= "{" Word "|" Word "|" WordStack "}"
    syntax CallLog ::= ".CallLog" | Call ";" CallLog
 // ------------------------------------------------

    syntax Bool ::= Call "in" CallLog [function]
 // --------------------------------------------
    rule C      in .CallLog       => false
    rule C:Call in (C':Call ; CL) => C ==K C' orElseBool C in CL


// -   `#call_____` takes the calling account, the account to execute as, the code
//     to execute, the amount to transfer, and the arguments.

// TODO: `#call` is neutured to make sure that we can pass the VMTests. The
// following is closer to what it should be.

// Here is what we're actually using. The test-set isn't clear about whach should
// happen when `#call` is run, but it seems that it should push `1` onto the stack.


    syntax InternalOp ::= "#call" Word Word Map Word WordStack
 // ----------------------------------------------------------
    rule <op> #call ACCTFROM ACCTTO CODE VALUE ARGS => 1 ~> #push ... </op>
         <callStack> CS </callStack>
         <callLog> CL => { ACCTTO | VALUE | ARGS } ; CL </callLog>
         <account>
           <acctID>  ACCTFROM </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires word2Bool(VALUE <=Word BAL) andBool (#size(CS) <Int 1024)

    rule <op> #call ACCTFROM ACCTTO CODE VALUE ARGS => #exception ... </op>
         <account>
           <acctID> ACCTFROM </acctID>
           <balance> BAL </balance>
           ...
         </account>
      requires word2Bool(VALUE >Word BAL)

    rule <op> #call ACCTFROM ACCTTO CODE VALUE ARGS => #exception ... </op>
         <callStack> CS </callStack>
      requires #size(CS) >Int 1024

    syntax CallOp ::= "CALL"
 // ------------------------
    rule <op> CALL GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #call ACCTFROM #addr(ACCTTO) CODE VALUE #range(LM, ARGSTART, ARGWIDTH)
           ~> #returnLoc RETSTART RETWIDTH
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH) </memoryUsed>
         <account>
           <acctID> ACCTTOACT </acctID>
           <code> CODE </code>
           ...
         </account>
      requires #addr(ACCTTO) ==K ACCTTOACT

    syntax CallOp ::= "CALLCODE"
 // ----------------------------
    rule <op> CALLCODE GASCAP ACCTTO VALUE ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #call ACCTFROM ACCTFROM CODE VALUE #range(LM, ARGSTART, ARGWIDTH)
           ~> #returnLoc RETSTART RETWIDTH
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH) </memoryUsed>
         <account>
           <acctID> ACCTTOACT </acctID>
           <code> CODE </code>
           ...
         </account>
      requires #addr(ACCTTO) ==K ACCTTOACT

    syntax CallOp ::= "DELEGATECALL"
 // --------------------------------
    rule <op> DELEGATECALL GASCAP ACCTTO ARGSTART ARGWIDTH RETSTART RETWIDTH
           => #call ACCTFROM ACCTFROM CODE 0 #range(LM, ARGSTART, ARGWIDTH)
           ~> #returnLoc RETSTART RETWIDTH
           ...
         </op>
         <id> ACCTFROM </id>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(#memoryUsageUpdate(MU, ARGSTART, ARGWIDTH), RETSTART, RETWIDTH) </memoryUsed>
         <account>
           <acctID> ACCTTOACT </acctID>
           <code> CODE </code>
           ...
         </account>
      requires #addr(ACCTTO) ==K ACCTTOACT

    syntax UnStackOp ::= "SELFDESTRUCT"
 // -----------------------------------
    rule <op> SELFDESTRUCT ACCTTO => . ... </op>
         <id> ACCT </id>
         <selfDestruct> SDS (.Set => SetItem(ACCT)) </selfDestruct>
         <refund> RF => #ifWord ACCT in SDS #then RF #else RF +Word Rself-destruct #fi </refund>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM => 0 </balance>
           ...
         </account>
         <account>
           <acctID> ACCTTOACT </acctID>
           <balance> BALTO => BALTO +Word BALFROM </balance>
           ...
         </account>
      requires #addr(ACCTTO) ==K ACCTTOACT

    rule <op> SELFDESTRUCT ACCTTO => #newAccount #addr(ACCTTO) ... </op>
         <id> ACCT </id>
         <selfDestruct> SDS (.Set => SetItem(ACCT)) </selfDestruct>
         <refund> RF => #ifWord ACCT in SDS #then RF #else RF +Word Rself-destruct #fi </refund>
         <activeAccounts> ACCTS (.Set => SetItem(#addr(ACCTTO))) </activeAccounts>
         <account>
           <acctID> ACCT </acctID>
           <balance> BALFROM => 0 </balance>
           ...
         </account>
      requires notBool #addr(ACCTTO) in ACCTS

    syntax Word        ::= #newAddr ( Word , Word )
    syntax InternalOp  ::= "#codeDeposit"
    syntax TernStackOp ::= "CREATE"
 // -------------------------------
    rule <op> CREATE VALUE MEMSTART MEMWIDTH
           => #call ACCT #newAddr(ACCT, NONCE) #asMap(#dasmOpCodes(#range(LM, MEMSTART, MEMWIDTH))) VALUE .WordStack
           ~> #codeDeposit
          ...
         </op>
         <id> ACCT </id>
         <callStack> CS </callStack>
         <localMem> LM </localMem>
         <memoryUsed> MU => #memoryUsageUpdate(MU, MEMSTART, MEMWIDTH) </memoryUsed>
         <activeAccounts> ACCTS </activeAccounts>
         <account>
           <acctID> ACCT </acctID>
           <balance> BAL => BAL -Word VALUE </balance>
           <acctMap> ... "nonce" |-> (NONCE => NONCE +Int 1) ... </acctMap>
           ...
         </account>
      requires #size(CS) <Int 1024 andBool word2Bool(BAL >=Word VALUE)


// Ethereum Gas Calculation
// ========================

// The gas calculation is designed to mirror the style of the yellowpaper.


    syntax Word ::= "Gzero" | "Gbase" | "Gverylow" | "Glow" | "Gmid" | "Ghigh" | "Gextcode"
                  | "Gbalance" | "Gsload" | "Gjumpdest" | "Gsset" | "Gsreset" | "Rsclear"
                  | "Rself-destruct" | "Gself-destruct" | "Gcreate" | "Gcodedeposit" | "Gcall"
                  | "Gcallvalue" | "Gcallstipend" | "Gnewaccount" | "Gexp" | "Gexpbyte"
                  | "Gmemory" | "Gtxcreate" | "Gtxdatazero" | "Gtxdatanonzero" | "Gtransaction"
                  | "Glog" | "Glogdata" | "Glogtopic" | "Gsha3" | "Gsha3word" | "Gcopy" | "Gblockhash"
                  | "#gasSSTORE" | "#gasCALL" | "#gasSELFDESTRUCT"
 // --------------------------------------------------------------
    rule Gzero          => 0        [macro]
    rule Gbase          => 2        [macro]
    rule Gverylow       => 3        [macro]
    rule Glow           => 5        [macro]
    rule Gmid           => 8        [macro]
    rule Ghigh          => 10       [macro]
    rule Gextcode       => 700      [macro]
    rule Gbalance       => 400      [macro]
    rule Gsload         => 200      [macro]
    rule Gjumpdest      => 1        [macro]
    rule Gsset          => 20000    [macro]
    rule Gsreset        => 5000     [macro]
    rule Rsclear        => 15000    [macro]
    rule Rself-destruct => 24000    [macro]
    rule Gself-destruct => 5000     [macro]
    rule Gcreate        => 32000    [macro]
    rule Gcodedeposit   => 200      [macro]
    rule Gcall          => 700      [macro]
    rule Gcallvalue     => 9000     [macro]
    rule Gcallstipend   => 2300     [macro]
    rule Gnewaccount    => 25000    [macro]
    rule Gexp           => 10       [macro]
    rule Gexpbyte       => 10       [macro]
    rule Gmemory        => 3        [macro]
    rule Gtxcreate      => 32000    [macro]
    rule Gtxdatazero    => 4        [macro]
    rule Gtxdatanonzero => 68       [macro]
    rule Gtransaction   => 21000    [macro]
    rule Glog           => 375      [macro]
    rule Glogdata       => 8        [macro]
    rule Glogtopic      => 375      [macro]
    rule Gsha3          => 30       [macro]
    rule Gsha3word      => 6        [macro]
    rule Gcopy          => 3        [macro]
    rule Gblockhash     => 20       [macro]

    syntax OpCodes ::= "Wzero" | "Wbase" | "Wverylow" | "Wlow" | "Wmid" | "Whigh" | "Wextcode" | "Wcopy" | "Wcall"
 // --------------------------------------------------------------------------------------------------------------
    rule Wzero    => STOP ; RETURN ; .OpCodes                                               [macro]
    rule Wbase    =>   ADDRESS ; ORIGIN ; CALLER ; CALLVALUE ; CALLDATASIZE
                     ; CODESIZE ; GASPRICE ; COINBASE ; TIMESTAMP ; NUMBER
                     ; DIFFICULTY ; GASLIMIT ; POP ; PC ; MSIZE ; GAS ; .OpCodes            [macro]
    rule Wverylow =>   ADD ; SUB ; NOT ; LT ; GT ; SLT ; SGT ; EQ ; ISZERO ; AND
                     ; EVMOR ; XOR ; BYTE ; CALLDATALOAD ; MLOAD ; MSTORE ; MSTORE8
                     ; PUSH(0, 0) ; DUP(0) ; SWAP(0) ; .OpCodes                             [macro]
    rule Wlow     => MUL ; DIV ; SDIV ; MOD ; SMOD ; SIGNEXTEND ; .OpCodes                  [macro]
    rule Wmid     => ADDMOD ; MULMOD ; JUMP ; JUMPI; .OpCodes                               [macro]
    rule Wextcode => EXTCODESIZE ; .OpCodes                                                 [macro]
    rule Wcopy    => CALLDATACOPY ; CODECOPY ; .OpCodes                                     [macro]
    rule Wcall    => CALL ; CALLCODE ; DELEGATECALL ; .OpCodes                              [macro]


// TODO: The rules marked as `INCORRECT` below are performing simpler gas
// calculations than the actual yellowpaper specifies.


    syntax Word ::= #gas ( OpCode )
 // -------------------------------
    // rule <op> #gas(OP)           => ???                           ... </op> requires OP in Wcall
    // rule <op> #gas(SELFDESTRUCT) => ???                           ... </op>
    rule <op> #gas(EXP)          => Gexp                          ... </op>                        // INCORRECT
    rule <op> #gas(OP)           => Gverylow +Word Gcopy          ... </op> requires OP in Wcopy   // INCORRECT
    rule <op> #gas(EXTCODECOPY)  => Gextcode +Word Gcopy          ... </op>                        // INCORRECT
    rule <op> #gas(LOG(N))       => Glog +Word (N *Word Glogdata) ... </op>                        // INCORRECT
    rule <op> #gas(CREATE)       => Gcreate                       ... </op>
    rule <op> #gas(SHA3)         => Gsha3                         ... </op>                        // INCORRECT
    rule <op> #gas(JUMPDEST)     => Gjumpdest                     ... </op>

    rule <op> #gas(SLOAD)  => Gsload  ... </op>
    rule <op> #gas(SSTORE) => #if W1 =/=K 0 andBool notBool W0 in keys(STORAGE) #then Gsset #else Gsreset #fi ... </op>
         <wordStack> W0 : W1 : WS </wordStack> <storage> STORAGE </storage>

    rule <op> #gas(OP)           => Gzero                         ... </op> requires OP in Wzero
    rule <op> #gas(OP)           => Gbase                         ... </op> requires OP in Wbase
    rule <op> #gas(OP)           => Gverylow                      ... </op> requires OP in Wverylow
    rule <op> #gas(OP)           => Glow                          ... </op> requires OP in Wlow
    rule <op> #gas(OP)           => Gmid                          ... </op> requires OP in Wmid
    rule <op> #gas(OP)           => Ghigh                         ... </op> requires OP in Whigh
    rule <op> #gas(OP)           => Gextcode                      ... </op> requires OP in Wextcode
    rule <op> #gas(BALANCE)      => Gbalance                      ... </op>
    rule <op> #gas(BLOCKHASH)    => Gblockhash                    ... </op>
endmodule

