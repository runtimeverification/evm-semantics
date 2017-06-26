defn_files=k/ethereum.k k/data.k k/evm.k k/krypto.k
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
K:=$(shell krun --version)

passing_test_file=tests/passing.expected
passing_tests=$(shell cat ${passing_test_file})
passing_targets=${passing_tests:=.test}

test: $(passing_targets)

tests/tests-develop/%.test: tests/tests-develop/% build
	./evm $<

codeship: build split-tests
	./Build passing

.PHONY: all defn build split-tests ktest

tests/tests-develop/%/make.timestamp: tests/ethereum-tests/%.json
	@echo "==   split: $@"
	mkdir -p $(dir $@)
	tests/split-test.py $< $(dir $@) tests/templates/output.txt
	cp tests/templates/config.xml $(dir $@)
	touch $@

ifneq (,$(findstring RV-K, $(K)))
k/ethereum-kompiled/extras/timestamp: k/ethereum-kompiled/interpreter
k/ethereum-kompiled/interpreter: $(defn_files)
	@echo "== kompile: $@"
	@echo "== Detected RV-K, kompile will use $(K)"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory k \
					--hook-namespaces KRYPTO --gen-ml-only -O2
	ocamlfind opt -c k/ethereum-kompiled/constants.ml -package gmp -package zarith
	ocamlfind opt -c -I k/ethereum-kompiled KRYPTO.ml -package cryptokit
	ocamlfind opt -a -o semantics.cmxa KRYPTO.cmx
	ocamlfind remove ethereum-semantics-plugin
	ocamlfind install ethereum-semantics-plugin META semantics.cmxa semantics.a KRYPTO.cmi KRYPTO.cmx
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory k \
					--hook-namespaces KRYPTO --packages ethereum-semantics-plugin -O2
	cd k/ethereum-kompiled && ocamlfind opt -o interpreter constants.cmx prelude.cmx plugin.cmx parser.cmx lexer.cmx run.cmx interpreter.ml -package gmp -package dynlink -package zarith -package str -package uuidm -package unix -linkpkg -inline 20 -nodynlink -O3
else
k/ethereum-kompiled/extras/timestamp: $(defn_files)
	@echo "== kompile: $@"
	@echo "== Detected UIUC-K, kompile will use $(K)"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory k
endif

k/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p k
	pandoc-tangle --from markdown --to code-k --code k $< > $@

ktest: $(ktest_file)
	cd k; ktest $(realpath .)/$< 

tests/ethereum-tests/%.json:
	@echo "==  git submodule: cloning upstreams test repository"
	git submodule update --init

clean: 
	rm -r k/*
