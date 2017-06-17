defn_files=k/ethereum.k k/data.k k/evm-dasm.k k/evm.k

all: k/ethereum-kompiled/timestamp
defn: $(defn_files)
build: k/ethereum-kompiled/timestamp
.PHONY: all defn

k/ethereum-kompiled/timestamp: $(defn_files)
	@echo "== kompile: $@"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory k

k/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p k
	pandoc-tangle --from markdown --to code-k --code k $< > $@
