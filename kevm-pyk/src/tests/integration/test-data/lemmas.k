requires "../contracts.k"

module SUM-TO-N-INVARIANT

  imports LOOPSTEST-CONTRACT

  rule N xorInt maxUInt256 => maxUInt256 -Int N 
  requires #rangeUInt(256, N)
  [simplification]

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
