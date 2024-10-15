requires "domains.md"
requires "evm.md"

module ERC20TRANSFERVALID-SUMMARY
	imports EVM

	rule [program.load]:
		<k> #loadProgram BYTES => .K ...</k>
		<program> _ => BYTES </program>
		<jumpDests> _ => b"\x00\x00\x00\x00\x00\x00\x00\x00\x00" </jumpDests> [priority(40)]
endmodule

module SUMMARIES
    imports ERC20TRANSFERVALID-SUMMARY
endmodule