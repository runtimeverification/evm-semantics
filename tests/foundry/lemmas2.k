requires "foundry.md"

module LEMMAS2
    imports FOUNDRY

	rule #lookup ( STORAGE , I ) => 3
		requires #lookup ( STORAGE , I ) ==Int 3
	    [simplification]

endmodule