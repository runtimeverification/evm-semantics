KEVM Gas
========

Here is a representation of `Gas`. This sort is used by `<gas>`, `<callGas>`, and `<gasUsed>` cells of the EVM configuration. As is in this file, `Gas` is a super-sort of `Int` with no differing behaviour. However the distinction at this level allows for an extension of infinite gas later, see `infinite-gas.md`.

```k
module GAS-SYNTAX
    imports INT-SYNTAX
    
    syntax Gas ::= Int
    syntax Int ::= "gas2Int" "(" Gas ")" [function, total]
    
    syntax Gas ::= "minGas" "(" Gas "," Gas ")" [function, total]
                 > left:
                   Gas "*Gas" Gas [function, left, total]
                 | Gas "/Gas" Gas [function, left]
                 > left:
                   Gas "+Gas" Gas [function, left, total]
                 | Gas "-Gas" Gas [function, left, total]

    syntax Bool ::= Gas  "<Gas" Gas [function, left, total]
                  | Gas "<=Gas" Gas [function, left, total]
endmodule

module GAS
    imports INT
    imports BOOL
    imports GAS-SYNTAX
    imports GAS-SIMPLIFICATION
    
    rule I1:Int *Gas I2:Int => I1 *Int I2
    rule I1:Int /Gas I2:Int => I1 /Int I2
    rule I1:Int +Gas I2:Int => I1 +Int I2
    rule I1:Int -Gas I2:Int => I1 -Int I2
    
    rule I1:Int  <Gas I2:Int => I1  <Int I2
    rule I1:Int <=Gas I2:Int => I1 <=Int I2
    
    rule minGas(I1:Int, I2:Int) => minInt(I1, I2)
    rule gas2Int(G:Int) => G
endmodule

module GAS-SIMPLIFICATION [symbolic]
    imports GAS-SYNTAX
    imports INT
    imports BOOL

    rule A  <Gas B => false requires B <=Gas A [simplification]
endmodule
```