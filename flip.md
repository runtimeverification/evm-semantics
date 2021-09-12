```k
module ABSTRACT-FLIP
    imports INT
```

Flip Configuration
------------------

```k
    configuration
      <flip>
          <flip-ttl> 21600:Int </flip-ttl>  // Bid Duration         - ETH A FLIP TTL @ 1630508398 UNIX TIME
          <flip-tau> 21600:Int </flip-tau>  // Total Auction Length - ETH A FLIP Tau @ 1630508398 UNIX TIME
      </flip>
```

### Abstract Contract Storage

```k
    syntax ContractStorage ::= #storageFlip(FlipCell)
```

### Storage Lookup
```
    rule #lookup(#storageFlip(<flip> ... <flip-tau> FLIP_TAU </flip-tau> ... </flip>), 5 ) => FLIP_TAU [simplification]
```

```k
endmodule
```
