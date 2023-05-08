K Helper Functions
------------------

```k
module K-UTILS
  imports INT
  imports LIST
```

### `List` utils

```k
    syntax List ::= qsort ( List ) [function]
 // -----------------------------------------
    rule qsort ( .List )           => .List
    rule qsort (ListItem(I:Int) L) => qsort(getIntElementsSmallerThan(I, L, .List)) ListItem(I) qsort(getIntElementsGreaterThan(I, L, .List))

    syntax List ::= getIntElementsSmallerThan ( Int, List, List ) [function]
                  | getIntElementsGreaterThan ( Int, List, List ) [function]
 // ------------------------------------------------------------------------
    rule getIntElementsSmallerThan (_, .List,               RESULTS) => RESULTS
    rule getIntElementsSmallerThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsSmallerThan (X, L, ListItem(I) RESULTS) requires I  <Int X
    rule getIntElementsSmallerThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsSmallerThan (X, L, RESULTS)             requires I >=Int X

    rule getIntElementsGreaterThan (_, .List ,              RESULTS) => RESULTS
    rule getIntElementsGreaterThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsGreaterThan (X, L, ListItem(I) RESULTS) requires I  >Int X
    rule getIntElementsGreaterThan (X, (ListItem(I:Int) L), RESULTS) => getIntElementsGreaterThan (X, L, RESULTS)             requires I <=Int X

```

```k
endmodule
```
