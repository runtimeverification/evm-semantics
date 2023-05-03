requires "../contracts.k"

module TEST-HELPER-LEMMAS
  imports ASSERTTEST-CONTRACT

  syntax Bytes ::= testFunction() [function]
  syntax Set ::= testFunction2(Bytes) [function]

  rule testFunction() => AssertTest.test_assert_true() [simplification]
  rule testFunction() => #binRuntime(AssertTest) [simplification]
  rule testFunction2(PGM) => #computeValidJumpDests(PGM) [simplification]

endmodule

module SUM-TO-N-INVARIANT

  imports LOOPSTEST-CONTRACT

    rule N xorInt maxUInt256 <Int S => false
    requires #rangeUInt(256, S +Int ((N *Int (N +Int 1)) /Int 2))
    andBool #rangeUInt(256, S)
    andBool #rangeUInt(256, N)
    [simplification]

    rule (S +Int N) +Int (((N -Int 1) *Int N) /Int 2) <Int pow256 => true
    requires #rangeUInt(256, S +Int ((N *Int (N +Int 1)) /Int 2))
    andBool #rangeUInt(256, S)
    andBool #rangeUInt(256, N)
    [simplification]

    rule chop(S +Int N) => S +Int N
    requires #rangeUInt(256, S +Int ((N *Int (N +Int 1)) /Int 2))
    andBool #rangeUInt(256, S)
    andBool #rangeUInt(256, N)
    [simplification]

    rule chop(N +Int -1) => N +Int -1
    requires 1 <=Int N andBool N <Int pow256
    andBool #rangeUInt(256, N)
    [simplification]

    rule (N *Int (N +Int 1)) /Int 2 <Int 115792089237316195423570985008687907853269984665640564039457584007913129639936 => true
    requires N <Int 481231938336009023090067544955250113853
    [simplification]

    rule 0 <=Int (N *Int (N +Int 1)) /Int 2 => true
    requires 0 <=Int N
    [simplification]

    rule N *Int 178 <=Int V => N <=Int V /Int 178
    [simplification]

//     rule N *Int 178 <=Int 9223372036854772639 => true
//     requires N <=Int 1641760222560149529742
//     [simplification]

  rule [foundry-sum-to-n-loop-invariant]:
  <kevm>
    <k>
      ((JUMPI 1569 CONDITION) => JUMP 1569)
      ~> #pc [ JUMPI ]
      ~> #execute
      ...
    </k>
    <mode>
      NORMAL
    </mode>
    <schedule>
      LONDON
    </schedule>
    <ethereum>
      <evm>
        <callState>
          <program>
            PROGRAM
          </program>
          <jumpDests>
            JUMPDESTS
          </jumpDests>
          <wordStack>
              (S => (S +Int ((N *Int (N +Int 1)) /Int 2)))
            : 0 
            : (N => 0)
            : 334 
            : 2123244496 
            : .WordStack
          </wordStack>
          <pc>
            1539
          </pc>
          <gas>
            GAS_AMT:Int => GAS_AMT -Int (N *Int 178)
          </gas>
          ...
        </callState>
        ...
      </evm>
      ...
    </ethereum>
    ...
  </kevm>

  requires 0 <Int N
   andBool #rangeUInt(256, S +Int ((N *Int (N +Int 1)) /Int 2))
   andBool #rangeUInt(256, N)
   andBool #rangeUInt(256, S)
   andBool GAS_AMT >=Int N *Int 178
   andBool CONDITION ==K bool2Word ( N:Int ==Int 0 )
   andBool PROGRAM ==K #binRuntime(LoopsTest)
   andBool JUMPDESTS ==K #computeValidJumpDests(#binRuntime(LoopsTest))
  [priority(40)]

endmodule
