defn_files=k/ethereum.k k/data.k k/evm-dasm.k k/evm.k

build: k/ethereum-kompiled/timestamp
all: build split-tests
defn: $(defn_files)
split-tests: tests/tests-develop/VMTests/vmArithmeticTest/make.timestamp \
			 tests/tests-develop/VMTests/vmBitwiseLogicOperationTest/make.timestamp
.PHONY: all defn build split-tests

tests/tests-develop/%/make.timestamp: tests/ethereum-tests/%.json
	@echo "==   split: $@"
	mkdir -p $(dir $@)
	tests/split-test.py $< $(dir $@)
	touch $@

k/ethereum-kompiled/timestamp: $(defn_files)
	@echo "== kompile: $@"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory k

k/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p k
	pandoc-tangle --from markdown --to code-k --code k $< > $@
