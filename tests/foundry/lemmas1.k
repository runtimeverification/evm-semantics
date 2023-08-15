requires "foundry.md"

module LEMMAS1
    imports FOUNDRY

    syntax StepSort ::= Int
                      | Bool

    syntax KItem ::= runLemma ( StepSort )
                   | doneLemma( StepSort )

	rule <k> runLemma(T) => doneLemma(T) ... </k>
endmodule

module LEMMAS1-SPEC
	imports LEMMAS1

	claim [lookup-equals-3]: <k>
		runLemma ( chop ( 1 <<Int #lookup ( STORAGE:Map , 0 ) ) <=Int maxUInt64 ) =>
		doneLemma ( true ) ... </k>
		requires #lookup ( STORAGE , 0 ) ==Int 3

endmodule