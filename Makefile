defn_files=k/ethereum.k k/data.k k/evm.k
ktest_file=tests/config.xml

build: k/ethereum-kompiled/extras/timestamp
all: build split-tests
defn: $(defn_files)
split-tests: tests/tests-develop/VMTests/vmArithmeticTest/make.timestamp \
			 tests/tests-develop/VMTests/vmBitwiseLogicOperationTest/make.timestamp \
			 tests/tests-develop/VMTests/vmBlockInfoTest/make.timestamp \
			 tests/tests-develop/VMTests/vmEnvironmentalInfoTest/make.timestamp \
			 tests/tests-develop/VMTests/vmIOandFlowOperationsTest/make.timestamp \
			 tests/tests-develop/VMTests/vmLogTest/make.timestamp \
			 tests/tests-develop/VMTests/vmPerformanceTest/make.timestamp \
			 tests/tests-develop/VMTests/vmPushDupSwapTest/make.timestamp \
			 tests/tests-develop/VMTests/vmSha3Test/make.timestamp \
			 tests/tests-develop/VMTests/vmSystemOperationsTest/make.timestamp \
			 tests/tests-develop/VMTests/vmtests/make.timestamp

ktest: defn split-tests 

.PHONY: all defn build split-tests ktest

tests/tests-develop/%/make.timestamp: tests/ethereum-tests/%.json
	@echo "==   split: $@"
	mkdir -p $(dir $@)
	tests/split-test.py $< $(dir $@) tests/templates/output.txt
	cp tests/templates/config.xml $(dir $@)
	touch $@

k/ethereum-kompiled/extras/timestamp: $(defn_files)
	@echo "== kompile: $@"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory k

k/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p k
	pandoc-tangle --from markdown --to code-k --code k $< > $@

ktest: $(ktest_file)
	cd k; ktest $(realpath .)/$< 

tests/ethereum-tests/%.json:
	@echo "==  git submodule: cloning upstreams test repository"
	git submodule update --init
