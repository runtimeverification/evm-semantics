
defn_dir=k
defn_files=${defn_dir}/ethereum.k ${defn_dir}/data.k ${defn_dir}/evm.k ${defn_dir}/krypto.k
build: k/ethereum-kompiled/extras/timestamp
all: build split-tests
defn: $(defn_files)
split-tests: tests/VMTests/vmArithmeticTest/make.timestamp \
			 tests/VMTests/vmBitwiseLogicOperationTest/make.timestamp \
			 tests/VMTests/vmBlockInfoTest/make.timestamp \
			 tests/VMTests/vmEnvironmentalInfoTest/make.timestamp \
			 tests/VMTests/vmIOandFlowOperationsTest/make.timestamp \
			 tests/VMTests/vmLogTest/make.timestamp \
			 tests/VMTests/vmPerformanceTest/make.timestamp \
			 tests/VMTests/vmPushDupSwapTest/make.timestamp \
			 tests/VMTests/vmSha3Test/make.timestamp \
			 tests/VMTests/vmSystemOperationsTest/make.timestamp \
			 tests/VMTests/vmtests/make.timestamp \
			 tests/VMTests/vmInputLimits/make.timestamp \
			 tests/VMTests/vmInputLimitsLight/make.timestamp

K:=$(shell krun --version)

.PHONY: all defn build split-tests

tests/%/make.timestamp: tests/ethereum-tests/%.json
	@echo "==   split: $@"
	mkdir -p $(dir $@)
	tests/split-test.py $< $(dir $@)
	touch $@

ifneq (,$(findstring RV-K, $(K)))
k/ethereum-kompiled/extras/timestamp: k/ethereum-kompiled/interpreter
k/ethereum-kompiled/interpreter: $(defn_files) KRYPTO.ml
	@echo "== kompile: $@"
	@echo "== Detected RV-K, kompile will use $(K)"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory k \
					--hook-namespaces KRYPTO --gen-ml-only -O3 --non-strict
	ocamlfind opt -c k/ethereum-kompiled/constants.ml -package gmp -package zarith
	ocamlfind opt -c -I k/ethereum-kompiled KRYPTO.ml -package cryptokit
	ocamlfind opt -a -o semantics.cmxa KRYPTO.cmx
	ocamlfind remove ethereum-semantics-plugin
	ocamlfind install ethereum-semantics-plugin META semantics.cmxa semantics.a KRYPTO.cmi KRYPTO.cmx
	cd $(dir $(shell which krun))/../include/ocaml/fakelibs && cp libffi.a libz.a
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory k \
					--hook-namespaces KRYPTO --packages ethereum-semantics-plugin -O3 --non-strict
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
ifneq (,$(findstring RV-K, $(K)))
	@echo "== Detected RV-K, will select codeblocks marked with 'rvk'"
	pandoc-tangle --from markdown --to code-k --code rvk $< > $@
else
	@echo "== Detected UIUC-K, will select codeblocks marked with 'uiuck'"
	pandoc-tangle --from markdown --to code-k --code uiuck $< > $@
endif

tests/ethereum-tests/%.json:
	@echo "==  git submodule: cloning upstreams test repository"
	git submodule update --init

clean: 
	rm -r k/*
