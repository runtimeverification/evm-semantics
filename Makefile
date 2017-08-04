ifndef K_VERSION
$(error K_VERSION not set. Please use the Build script, instead of running make directly)
endif

# Common to all versions of K
# ===========================

.PHONY: all defn build split-tests proofs

all: build split-tests

clean:
	rm -r .build
	find tests/proofs/ -name '*.k' -delete

build: tangle .build/${K_VERSION}/ethereum-kompiled/extras/timestamp

# Tangle from *.md files
# ----------------------

defn_dir=.build/${K_VERSION}
defn_files=${defn_dir}/ethereum.k ${defn_dir}/data.k ${defn_dir}/evm.k ${defn_dir}/analysis.k ${defn_dir}/krypto.k ${defn_dir}/verification.k

tangle: defn proofs
defn: $(defn_files)

.build/${K_VERSION}/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc-tangle --from markdown --to code-k --code ${K_VERSION} $< > $@

proofs: tests/proofs/hkg/transferFrom-then-spec.k \
		tests/proofs/hkg/transferFrom-else-spec.k \
		tests/proofs/hkg/transfer-then-spec.k \
		tests/proofs/hkg/transfer-else-spec.k

tests/proofs/hkg/transferFrom-then-spec.k: proofs/hkg/transferFrom.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc-tangle --from markdown --to code-k --code k --section "Then Branch" $< > $@

tests/proofs/hkg/transferFrom-else-spec.k: proofs/hkg/transferFrom.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc-tangle --from markdown --to code-k --code k --section "Else Branch" $< > $@

tests/proofs/hkg/transfer-then-spec.k: proofs/hkg/transfer.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc-tangle --from markdown --to code-k --code k --section "Then Branch" $< > $@

tests/proofs/hkg/transfer-else-spec.k: proofs/hkg/transfer.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc-tangle --from markdown --to code-k --code k --section "Else Branch" $< > $@

# Tests
# -----

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

tests/%/make.timestamp: tests/ethereum-tests/%.json
	@echo "==   split: $@"
	mkdir -p $(dir $@)
	tests/split-test.py $< $(dir $@)
	touch $@

tests/ethereum-tests/%.json:
	@echo "==  git submodule: cloning upstreams test repository"
	git submodule update --init

# UIUC K Specific
# ---------------

.build/uiuck/ethereum-kompiled/extras/timestamp: $(defn_files)
	@echo "== kompile: $@"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/uiuck

# RVK Specific
# ------------

.build/rvk/ethereum-kompiled/extras/timestamp: .build/rvk/ethereum-kompiled/interpreter
.build/rvk/ethereum-kompiled/interpreter: $(defn_files) KRYPTO.ml
	@echo "== kompile: $@"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/rvk \
					--hook-namespaces KRYPTO --gen-ml-only -O3 --non-strict
	ocamlfind opt -c .build/rvk/ethereum-kompiled/constants.ml -package gmp -package zarith
	ocamlfind opt -c -I .build/rvk/ethereum-kompiled KRYPTO.ml -package cryptokit
	ocamlfind opt -a -o semantics.cmxa KRYPTO.cmx
	ocamlfind remove ethereum-semantics-plugin
	ocamlfind install ethereum-semantics-plugin META semantics.cmxa semantics.a KRYPTO.cmi KRYPTO.cmx
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/rvk \
					--hook-namespaces KRYPTO --packages ethereum-semantics-plugin -O3 --non-strict
	cd .build/rvk/ethereum-kompiled && ocamlfind opt -o interpreter constants.cmx prelude.cmx plugin.cmx parser.cmx lexer.cmx run.cmx interpreter.ml -package gmp -package dynlink -package zarith -package str -package uuidm -package unix -linkpkg -inline 20 -nodynlink -O3
