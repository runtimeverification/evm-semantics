# Settings
# --------

BUILD_DIR:=$(CURDIR)/.build
BUILD_LOCAL:=$(BUILD_DIR)/local
LIBRARY_PATH:=$(BUILD_LOCAL)/lib
PKG_CONFIG_PATH:=$(LIBRARY_PATH)/pkgconfig
export LIBRARY_PATH
export PKG_CONFIG_PATH

K_SUBMODULE:=$(BUILD_DIR)/k
PLUGIN_SUBMODULE:=$(abspath plugin)

# need relative path for `pandoc` on MacOS
PANDOC_TANGLE_SUBMODULE:=.build/pandoc-tangle
TANGLER:=$(PANDOC_TANGLE_SUBMODULE)/tangle.lua
LUA_PATH:=$(PANDOC_TANGLE_SUBMODULE)/?.lua;;
export TANGLER
export LUA_PATH

KORE_SUBMODULE:=$(BUILD_DIR)/kore
KORE_SUBMODULE_SRC:=$(KORE_SUBMODULE)/src/main/haskell/kore

.PHONY: all clean deps repo-deps system-deps k-deps tangle-deps ocaml-deps plugin-deps kore-deps \
		build build-ocaml build-java build-node build-kore split-tests \
		defn java-defn ocaml-defn node-defn haskell-defn \
		test test-all test-concrete test-all-concrete test-conformance test-slow-conformance test-all-conformance \
		test-vm test-slow-vm test-all-vm test-bchain test-slow-bchain test-all-bchain \
		test-proof test-interactive test-vm-normal \
		metropolis-theme 2017-devcon3 sphinx
.SECONDARY:

all: build split-tests

clean: clean-submodules
	rm -rf .build/java .build/plugin-ocaml .build/plugin-node .build/ocaml .build/haskell .build/llvm .build/node .build/logs .build/local .build/vm tests/proofs/specs

clean-submodules:
	rm -rf .build/k/make.timestamp .build/pandoc-tangle/make.timestamp tests/ethereum-tests/make.timestamp tests/proofs/make.timestamp plugin/make.timestamp kore/make.timestamp .build/media/metropolis/*.sty

distclean: clean
	opam switch system
	opam switch remove 4.03.0+k --yes || true
	cd $(K_SUBMODULE) \
		&& mvn clean -q
	git submodule deinit --force -- ./

# Dependencies
# ------------

deps: repo-deps system-deps
repo-deps: tangle-deps k-deps plugin-deps
system-deps: ocaml-deps
haskell-deps: tangle-deps k-deps kore-deps
k-deps: $(K_SUBMODULE)/make.timestamp
tangle-deps: $(PANDOC_TANGLE_SUBMODULE)/make.timestamp
plugin-deps: $(PLUGIN_SUBMODULE)/make.timestamp
kore-deps: $(KORE_SUBMODULE)/make.timestamp

$(K_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init -- $(K_SUBMODULE)
	cd $(K_SUBMODULE) \
		&& mvn package -q -DskipTests -U
	touch $(K_SUBMODULE)/make.timestamp

$(PANDOC_TANGLE_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init -- $(PANDOC_TANGLE_SUBMODULE)
	touch $(PANDOC_TANGLE_SUBMODULE)/make.timestamp

$(PLUGIN_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init --recursive -- $(PLUGIN_SUBMODULE)
	touch $(PLUGIN_SUBMODULE)/make.timestamp

$(KORE_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init -- $(KORE_SUBMODULE)
	cd $(KORE_SUBMODULE) \
		&& stack install --local-bin-path $(abspath $(KORE_SUBMODULE))/bin kore:exe:kore-exec
	touch ${KORE_SUBMODULE}/make.timestamp

ocaml-deps: .build/local/lib/pkgconfig/libsecp256k1.pc
	opam init --quiet --no-setup
	opam repository add k "$(K_SUBMODULE)/k-distribution/target/release/k/lib/opam" \
		|| opam repository set-url k "$(K_SUBMODULE)/k-distribution/target/release/k/lib/opam"
	opam update
	opam switch 4.06.1+k
	eval $$(opam config env) \
		opam install --yes mlgmp zarith uuidm cryptokit secp256k1.0.3.2 bn128 ocaml-protoc rlp yojson hex ocp-ocamlres

# install secp256k1 from bitcoin-core
.build/local/lib/pkgconfig/libsecp256k1.pc:
	@echo "== submodule: $@"
	git submodule update --init -- .build/secp256k1/
	cd .build/secp256k1/ \
		&& ./autogen.sh \
		&& ./configure --enable-module-recovery --prefix="$(BUILD_LOCAL)" \
		&& make -s -j4 \
		&& make install

K_BIN=$(K_SUBMODULE)/k-distribution/target/release/k/bin

# Building
# --------

build: build-ocaml build-java build-node
build-ocaml: .build/ocaml/driver-kompiled/interpreter
build-java: .build/java/driver-kompiled/timestamp
build-node: .build/vm/kevm-vm
build-haskell: .build/haskell/driver-kompiled/definition.kore
build-llvm: .build/llvm/driver-kompiled/interpreter

# Tangle definition from *.md files

standalone_tangle:=.k:not(.node),.standalone
node_tangle:=.k:not(.standalone),.node

k_files:=driver.k data.k network.k evm.k analysis.k krypto.k edsl.k evm-node.k
ocaml_files:=$(patsubst %,.build/ocaml/%,$(k_files))
java_files:=$(patsubst %,.build/java/%,$(k_files))
node_files:=$(patsubst %,.build/node/%,$(k_files))
haskell_files:=$(patsubst %,.build/haskell/%,$(k_files))
defn_files:=$(ocaml_files) $(java_files) $(node_files)

defn: $(defn_files)
java-defn: $(java_files)
ocaml-defn: $(ocaml_files)
node-defn: $(node_files)
haskell-defn: $(haskell_files)

.build/java/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(standalone_tangle)" $< > $@

.build/ocaml/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(standalone_tangle)" $< > $@

.build/node/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(node_tangle)" $< > $@

.build/haskell/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(standalone_tangle)" $< > $@

# Java Backend

.build/java/driver-kompiled/timestamp: $(java_files)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module ETHEREUM-SIMULATION --backend java \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/java -I .build/java

# Haskell Backend

.build/haskell/driver-kompiled/definition.kore: $(haskell_files)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module ETHEREUM-SIMULATION --backend haskell \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/haskell -I .build/haskell

# OCAML Backend

ifeq ($(BYTE),yes)
  EXT=cmo
  LIBEXT=cma
  DLLEXT=cma
  OCAMLC=c
  LIBFLAG=-a
else
  EXT=cmx
  LIBEXT=cmxa
  DLLEXT=cmxs
  OCAMLC=opt -O3
  LIBFLAG=-shared
endif

.build/llvm/driver-kompiled/interpreter: $(ocaml_files)
	@echo "== kompile: $@"
	eval $$(opam config env) \
		&& ${K_BIN}/kompile --debug --main-module ETHEREUM-SIMULATION \
						    --syntax-module ETHEREUM-SIMULATION .build/ocaml/driver.k --directory .build/llvm \
						    --backend llvm -ccopt ${PLUGIN_SUBMODULE}/plugin-c/crypto.cpp \
						    -ccopt -lff -ccopt -lcryptopp -ccopt -lsecp256k1 -ccopt -lprocps -ccopt -g -ccopt -std=c++11 -ccopt -O2

.build/%/driver-kompiled/constants.$(EXT): $(ocaml_files) $(node_files)
	@echo "== kompile: $@"
	eval $$(opam config env) \
		&& ${K_BIN}/kompile --debug --main-module ETHEREUM-SIMULATION \
						    --syntax-module ETHEREUM-SIMULATION .build/$*/driver.k --directory .build/$* \
						    --hook-namespaces "KRYPTO BLOCKCHAIN" --gen-ml-only -O3 --non-strict \
		&& cd .build/$*/driver-kompiled \
		&& ocamlfind $(OCAMLC) -c -g constants.ml -package gmp -package zarith -safe-string

.build/plugin-%/semantics.$(LIBEXT): $(wildcard plugin/plugin/*.ml plugin/plugin/*.mli) .build/%/driver-kompiled/constants.$(EXT)
	mkdir -p .build/plugin-$*
	cp plugin/plugin/*.ml plugin/plugin/*.mli .build/plugin-$*
	eval $$(opam config env) \
		&& ocp-ocamlres -format ocaml plugin/plugin/proto/VERSION -o .build/plugin-$*/apiVersion.ml \
		&& ocaml-protoc plugin/plugin/proto/*.proto -ml_out .build/plugin-$* \
		&& cd .build/plugin-$* \
			&& ocamlfind $(OCAMLC) -c -g -I ../$*/driver-kompiled msg_types.mli msg_types.ml msg_pb.mli msg_pb.ml apiVersion.ml world.mli world.ml caching.mli caching.ml BLOCKCHAIN.ml KRYPTO.ml \
								   -package cryptokit -package secp256k1 -package bn128 -package ocaml-protoc -safe-string -thread \
			&& ocamlfind $(OCAMLC) -a -o semantics.$(LIBEXT) KRYPTO.$(EXT) msg_types.$(EXT) msg_pb.$(EXT) apiVersion.$(EXT) world.$(EXT) caching.$(EXT) BLOCKCHAIN.$(EXT) -thread \
			&& ocamlfind remove ethereum-semantics-plugin-$* \
			&& ocamlfind install ethereum-semantics-plugin-$* ../../plugin/plugin/META semantics.* *.cmi *.$(EXT)

.build/%/driver-kompiled/interpreter: .build/plugin-%/semantics.$(LIBEXT)
	eval $$(opam config env) \
		&& cd .build/$*/driver-kompiled \
			&& ocamllex lexer.mll \
			&& ocamlyacc parser.mly \
			&& ocamlfind $(OCAMLC) -c -g -package gmp -package zarith -package uuidm -safe-string prelude.ml plugin.ml parser.mli parser.ml lexer.ml run.ml -thread \
			&& ocamlfind $(OCAMLC) -c -g -w -11-26 -package gmp -package zarith -package uuidm -package ethereum-semantics-plugin-$* -safe-string realdef.ml -match-context-rows 2 \
			&& ocamlfind $(OCAMLC) $(LIBFLAG) -o realdef.$(DLLEXT) realdef.$(EXT) \
			&& ocamlfind $(OCAMLC) -g -o interpreter constants.$(EXT) prelude.$(EXT) plugin.$(EXT) parser.$(EXT) lexer.$(EXT) run.$(EXT) interpreter.ml \
								   -package gmp -package dynlink -package zarith -package str -package uuidm -package unix -package ethereum-semantics-plugin-$* -linkpkg -linkall -thread -safe-string

.build/vm/kevm-vm: $(wildcard plugin/vm/*.ml plugin/vm/*.mli) .build/node/driver-kompiled/interpreter
	mkdir -p .build/vm
	cp plugin/vm/*.ml plugin/vm/*.mli .build/vm
	eval $$(opam config env) \
		&& cd .build/vm \
			&& ocamlfind $(OCAMLC) -g -I ../node/driver-kompiled -o kevm-vm constants.$(EXT) prelude.$(EXT) plugin.$(EXT) parser.$(EXT) lexer.$(EXT) realdef.$(EXT) run.$(EXT) VM.mli VM.ml vmNetworkServer.ml \
								   -package gmp -package dynlink -package zarith -package str -package uuidm -package unix -package ethereum-semantics-plugin-node -package rlp -package yojson -package hex -linkpkg -linkall -thread -safe-string

# Tests
# -----

# Override this with `make TEST=echo` to list tests instead of running
TEST_BACKEND:=ocaml
TEST:=./kevm test-profile

test-all: test-all-concrete test-all-proof
test: test-concrete test-proof test-java

split-tests: tests/ethereum-tests/make.timestamp split-proof-tests

tests/%/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init -- tests/$*
	touch $@

# Concrete Tests

test-all-concrete: test-all-conformance test-interactive
test-concrete: test-conformance test-interactive

# Ethereum Tests

tests/ethereum-tests/%.json: tests/ethereum-tests/make.timestamp

test-all-conformance: test-all-vm test-all-bchain
test-slow-conformance: test-slow-vm test-slow-bchain
test-conformance: test-vm test-bchain

# VMTests

vm_tests=$(wildcard tests/ethereum-tests/VMTests/*/*.json)
slow_vm_tests=$(wildcard tests/ethereum-tests/VMTests/vmPerformance/*.json)
bad_vm_tests= $(wildcard tests/ethereum-tests/VMTests/vmBlockInfoTest/blockhash*.json) \
              $(wildcard tests/ethereum-tests/VMTests/vmEnvironmentalInfo/balance*.json) \
              $(wildcard tests/ethereum-tests/VMTests/vmSystemOperations/*call*.json) \
              $(wildcard tests/ethereum-tests/VMTests/vmSystemOperations/*Call*.json) \
              $(wildcard tests/ethereum-tests/VMTests/vmSystemOperations/*create*.json) \
              tests/ethereum-tests/VMTests/vmEnvironmentalInfo/env1.json \
              tests/ethereum-tests/VMTests/vmEnvironmentalInfo/extcodecopy0AddressTooBigRight.json \
              tests/ethereum-tests/VMTests/vmEnvironmentalInfo/ExtCodeSizeAddressInputTooBigRightMyAddress.json \
              tests/ethereum-tests/VMTests/vmRandomTest/201503102037PYTHON.json \
              tests/ethereum-tests/VMTests/vmRandomTest/201503102148PYTHON.json \
              tests/ethereum-tests/VMTests/vmRandomTest/201503102300PYTHON.json \
              tests/ethereum-tests/VMTests/vmRandomTest/201503110050PYTHON.json \
              tests/ethereum-tests/VMTests/vmRandomTest/201503110226PYTHON_DUP6.json \
              tests/ethereum-tests/VMTests/vmRandomTest/randomTest.json \
              tests/ethereum-tests/VMTests/vmSystemOperations/PostToNameRegistrator0.json \
              tests/ethereum-tests/VMTests/vmSystemOperations/PostToReturn1.json
all_vm_tests=$(filter-out $(bad_vm_tests), $(vm_tests))
quick_vm_tests=$(filter-out $(slow_vm_tests), $(all_vm_tests))

test-all-vm: $(all_vm_tests:=.test)
test-slow-vm: $(slow_vm_tests:=.test)
test-vm: $(quick_vm_tests:=.test)
test-vm-normal: $(quick_vm_tests:=.testnormal)

tests/ethereum-tests/VMTests/%.test: tests/ethereum-tests/VMTests/%
	MODE=VMTESTS SCHEDULE=DEFAULT $(TEST) --backend $(TEST_BACKEND) $<

tests/ethereum-tests/VMTests/%.testnormal: tests/ethereum-tests/VMTests/%
	SCHEDULE=DEFAULT $(TEST) --backend $(TEST_BACKEND) $<

# BlockchainTests

bchain_tests=$(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/*/*.json)
slow_bchain_tests=$(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call50000*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Return50000*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call1MB1024Calldepth_d1g0v0.json) \
		  tests/ethereum-tests/BlockchainTests/GeneralStateTests/stCreateTest/CREATE_ContractRETURNBigOffset_d2g0v0.json \
		  tests/ethereum-tests/BlockchainTests/GeneralStateTests/stCreateTest/CREATE_ContractRETURNBigOffset_d1g0v0.json
bad_bchain_tests= tests/ethereum-tests/BlockchainTests/GeneralStateTests/stCreate2/RevertOpcodeInCreateReturns_d0g0v0.json \
                  tests/ethereum-tests/BlockchainTests/GeneralStateTests/stCreate2/RevertInCreateInInit_d0g0v0.json
all_bchain_tests=$(filter-out $(bad_bchain_tests), $(bchain_tests))
quick_bchain_tests=$(filter-out $(slow_bchain_tests), $(all_bchain_tests))

test-all-bchain: $(all_bchain_tests:=.test)
test-slow-bchain: $(slow_bchain_tests:=.test)
test-bchain: $(quick_bchain_tests:=.test)

tests/ethereum-tests/BlockchainTests/%.test: tests/ethereum-tests/BlockchainTests/%
	$(TEST) --backend $(TEST_BACKEND) $<

# InteractiveTests

interactive_tests:=$(wildcard tests/interactive/*.json) \
                   $(wildcard tests/interactive/*/*.evm)

test-interactive: $(interactive_tests:=.test)

tests/interactive/%.json.test: tests/interactive/%.json
	$(TEST) --backend $(TEST_BACKEND) $<

tests/interactive/gas-analysis/%.evm.test: tests/interactive/gas-analysis/%.evm tests/interactive/gas-analysis/%.evm.out
	MODE=GASANALYZE $(TEST) --backend $(TEST_BACKEND) $<

# ProofTests

proof_dir:=tests/proofs/specs
proof_tests=$(wildcard $(proof_dir)/*/*-spec.k)

test-proof: $(proof_tests:=.test)

test-java: tests/ethereum-tests/BlockchainTests/GeneralStateTests/stExample/add11_d0g0v0.json
	./kevm run --backend java $< | diff - tests/templates/output-success-java.json

$(proof_dir)/%.test: $(proof_dir)/% split-proof-tests
	$(TEST) $<

split-proof-tests: tests/proofs/make.timestamp
	$(MAKE) -C tests/proofs $@

# Media
# -----

media: sphinx 2017-devcon3 2018-csf

# Presentations

metropolis-theme: $(BUILD_DIR)/media/metropolis/beamerthememetropolis.sty

$(BUILD_DIR)/media/metropolis/beamerthememetropolis.sty:
	@echo "== submodule: $@"
	git submodule update --init -- $(dir $@)
	cd $(dir $@) && make

2017-devcon3: $(BUILD_DIR)/media/2017-devcon3.pdf
2018-csf:     $(BUILD_DIR)/media/2018-csf.pdf

$(BUILD_DIR)/media/%.pdf: media/%.md media/citations.md
	@echo "== media: $@"
	mkdir -p $(dir $@)
	cat $^ | pandoc --from markdown --filter pandoc-citeproc --to beamer --output $@
	@echo "== $*: presentation generated at $@"

# Sphinx HTML Documentation

# You can set these variables from the command line.
SPHINXOPTS     =
SPHINXBUILD    = sphinx-build
PAPER          =
SPHINXBUILDDIR = .build/sphinx-docs

# Internal variables.
PAPEROPT_a4     = -D latex_paper_size=a4
PAPEROPT_letter = -D latex_paper_size=letter
ALLSPHINXOPTS   = -d ../$(SPHINXBUILDDIR)/doctrees $(PAPEROPT_$(PAPER)) $(SPHINXOPTS) .
# the i18n builder cannot share the environment and doctrees with the others
I18NSPHINXOPTS  = $(PAPEROPT_$(PAPER)) $(SPHINXOPTS) .

sphinx:
	@echo "== media: $@"
	mkdir -p $(SPHINXBUILDDIR) \
		&& cp -r *.md $(SPHINXBUILDDIR)/. \
		&& cd $(SPHINXBUILDDIR) \
		&& sed -i 's/{.k[ a-zA-Z.-]*}/k/g' *.md \
		&& $(SPHINXBUILD) -b dirhtml $(ALLSPHINXOPTS) html \
		&& $(SPHINXBUILD) -b text $(ALLSPHINXOPTS) html/text
	@echo "== sphinx: HTML generated in $(SPHINXBUILDDIR)/html, text in $(SPHINXBUILDDIR)/html/text"
