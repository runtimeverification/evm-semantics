requires "foundry.md"

module LEMMAS3
    imports FOUNDRY

	rule 1 <<Int X => 1 <<Int 3
		requires X ==Int 3
		[simplification]

endmodule