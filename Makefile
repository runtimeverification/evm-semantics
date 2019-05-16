# Settings
# --------

BUILD_DIR:=$(CURDIR)/.build
BUILD_LOCAL:=$(BUILD_DIR)/local
LIBRARY_PATH:=$(BUILD_LOCAL)/lib
C_INCLUDE_PATH:=$(BUILD_LOCAL)/include
CPLUS_INCLUDE_PATH:=$(BUILD_LOCAL)/include
PKG_CONFIG_PATH:=$(LIBRARY_PATH)/pkgconfig
export LIBRARY_PATH
export C_INCLUDE_PATH
export CPLUS_INCLUDE_PATH
export PKG_CONFIG_PATH

K_SUBMODULE:=$(BUILD_DIR)/k
PLUGIN_SUBMODULE:=$(abspath plugin)

# need relative path for `pandoc` on MacOS
PANDOC_TANGLE_SUBMODULE:=.build/pandoc-tangle
TANGLER:=$(PANDOC_TANGLE_SUBMODULE)/tangle.lua
LUA_PATH:=$(PANDOC_TANGLE_SUBMODULE)/?.lua;;
export TANGLER
export LUA_PATH

.PHONY: all clean deps all-deps llvm-deps haskell-deps repo-deps system-deps k-deps ocaml-deps plugin-deps libsecp256k1 libff \
        build build-ocaml build-java build-node build-kore split-tests \
        defn java-defn ocaml-defn node-defn haskell-defn \
        test test-all test-conformance test-slow-conformance test-all-conformance \
        test-vm test-slow-vm test-all-vm test-bchain test-slow-bchain test-all-bchain \
        test-proof test-parse test-interactive test-interactive-help test-interactive-run test-interactive-prove \
        metropolis-theme 2017-devcon3 sphinx
.SECONDARY:

all: build split-tests

clean: clean-submodules
	rm -rf .build/java .build/plugin-ocaml .build/plugin-node .build/ocaml .build/haskell .build/llvm .build/node .build/logs .build/vm tests/proofs/specs

clean-submodules:
	rm -rf .build/k/make.timestamp .build/pandoc-tangle/make.timestamp tests/ethereum-tests/make.timestamp tests/proofs/make.timestamp plugin/make.timestamp kore/make.timestamp .build/media/metropolis/*.sty

distclean: clean
	cd $(K_SUBMODULE) && mvn clean -q
	rm -rf .build/local
	git submodule deinit --force -- ./

# Dependencies
# ------------

all-deps: deps llvm-deps haskell-deps
all-deps: BACKEND_SKIP=
llvm-deps: .build/local/lib/libff.a deps
llvm-deps: BACKEND_SKIP=-Dhaskell.backend.skip
haskell-deps: deps
haskell-deps: BACKEND_SKIP=-Dllvm.backend.skip

deps: repo-deps system-deps
repo-deps: tangle-deps k-deps plugin-deps
system-deps: ocaml-deps
k-deps: $(K_SUBMODULE)/make.timestamp
tangle-deps: $(PANDOC_TANGLE_SUBMODULE)/make.timestamp
plugin-deps: $(PLUGIN_SUBMODULE)/make.timestamp

BACKEND_SKIP=-Dhaskell.backend.skip -Dllvm.backend.skip

$(K_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init --recursive -- $(K_SUBMODULE)
	cd $(K_SUBMODULE) && mvn package -DskipTests -U ${BACKEND_SKIP}
	touch $(K_SUBMODULE)/make.timestamp

K_BIN=$(K_SUBMODULE)/k-distribution/target/release/k/bin

$(PANDOC_TANGLE_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init -- $(PANDOC_TANGLE_SUBMODULE)
	touch $(PANDOC_TANGLE_SUBMODULE)/make.timestamp

$(PLUGIN_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init --recursive -- $(PLUGIN_SUBMODULE)
	touch $(PLUGIN_SUBMODULE)/make.timestamp

ocaml-deps:
	eval $$(opam config env) \
	    opam install --yes mlgmp zarith uuidm cryptokit secp256k1.0.3.2 bn128 ocaml-protoc rlp yojson hex ocp-ocamlres

# install secp256k1 from bitcoin-core
libsecp256k1: .build/local/lib/pkgconfig/libsecp256k1.pc

.build/local/lib/pkgconfig/libsecp256k1.pc:
	@echo "== submodule: .build/secp256k1"
	git submodule update --init -- .build/secp256k1/
	cd .build/secp256k1/ \
	    && ./autogen.sh \
	    && ./configure --enable-module-recovery --prefix="$(BUILD_LOCAL)" \
	    && make -s -j4 \
	    && make install

# install libff from scipr-lab
libff: .build/local/lib/libff.a

LIBFF_CC ?=clang-6.0
LIBFF_CXX?=clang++-6.0

.build/local/lib/libff.a:
	@echo "== submodule: .build/libff"
	git submodule update --init --recursive -- .build/libff/
	cd .build/libff/ \
	    && mkdir -p build \
	    && cd build \
	    && CC=$(LIBFF_CC) CXX=$(LIBFF_CXX) cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$(BUILD_LOCAL)" \
	    && make -s -j4 \
	    && make install

# Building
# --------

MAIN_MODULE:=ETHEREUM-SIMULATION
SYNTAX_MODULE:=$(MAIN_MODULE)
MAIN_DEFN_FILE:=driver
KOMPILE_OPTS:=

build: build-ocaml build-java
build-ocaml: .build/ocaml/$(MAIN_DEFN_FILE)-kompiled/interpreter
build-java: .build/java/$(MAIN_DEFN_FILE)-kompiled/timestamp
build-node: .build/vm/kevm-vm
build-haskell: .build/haskell/$(MAIN_DEFN_FILE)-kompiled/definition.kore
build-llvm: .build/llvm/$(MAIN_DEFN_FILE)-kompiled/interpreter

# Tangle definition from *.md files

concrete_tangle:=.k:not(.node):not(.symbolic),.standalone,.concrete
symbolic_tangle:=.k:not(.node):not(.concrete),.standalone,.symbolic
node_tangle:=.k:not(.standalone):not(.symbolic),.node,.concrete

k_files:=driver.k data.k network.k evm.k krypto.k edsl.k evm-node.k
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

.build/java/%.k: %.md $(PANDOC_TANGLE_SUBMODULE)/make.timestamp
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(symbolic_tangle)" $< > $@

.build/ocaml/%.k: %.md $(PANDOC_TANGLE_SUBMODULE)/make.timestamp
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(concrete_tangle)" $< > $@

.build/node/%.k: %.md $(PANDOC_TANGLE_SUBMODULE)/make.timestamp
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(node_tangle)" $< > $@

.build/haskell/%.k: %.md $(PANDOC_TANGLE_SUBMODULE)/make.timestamp
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(symbolic_tangle)" $< > $@

# Java Backend

.build/java/$(MAIN_DEFN_FILE)-kompiled/timestamp: $(java_files)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend java \
	                 --syntax-module $(SYNTAX_MODULE) .build/java/$(MAIN_DEFN_FILE).k --directory .build/java \
	                 -I .build/java $(KOMPILE_OPTS)

# Haskell Backend

.build/haskell/$(MAIN_DEFN_FILE)-kompiled/definition.kore: $(haskell_files)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend haskell --hook-namespaces KRYPTO \
	                 --syntax-module $(SYNTAX_MODULE) .build/haskell/$(MAIN_DEFN_FILE).k --directory .build/haskell \
	                 -I .build/haskell $(KOMPILE_OPTS)

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

.build/%/$(MAIN_DEFN_FILE)-kompiled/constants.$(EXT): $(ocaml_files)
	@echo "== kompile: $@"
	eval $$(opam config env) \
	    && ${K_BIN}/kompile --debug --main-module $(MAIN_MODULE) \
	                        --syntax-module $(SYNTAX_MODULE) .build/$*/$(MAIN_DEFN_FILE).k --directory .build/$* \
	                        --hook-namespaces "KRYPTO BLOCKCHAIN" --gen-ml-only -O3 --non-strict \
	                        -I .build/$* $(KOMPILE_OPTS) \
	    && cd .build/$*/$(MAIN_DEFN_FILE)-kompiled \
	    && ocamlfind $(OCAMLC) -c -g constants.ml -package gmp -package zarith -safe-string

.build/plugin-%/semantics.$(LIBEXT): $(wildcard plugin/plugin/*.ml plugin/plugin/*.mli) .build/%/$(MAIN_DEFN_FILE)-kompiled/constants.$(EXT)
	mkdir -p .build/plugin-$*
	cp plugin/plugin/*.ml plugin/plugin/*.mli .build/plugin-$*
	eval $$(opam config env) \
	    && ocp-ocamlres -format ocaml plugin/plugin/proto/VERSION -o .build/plugin-$*/apiVersion.ml \
	    && ocaml-protoc plugin/plugin/proto/*.proto -ml_out .build/plugin-$* \
	    && cd .build/plugin-$* \
	        && ocamlfind $(OCAMLC) -c -g -I ../$*/$(MAIN_DEFN_FILE)-kompiled msg_types.mli msg_types.ml msg_pb.mli msg_pb.ml apiVersion.ml world.mli world.ml caching.mli caching.ml BLOCKCHAIN.ml KRYPTO.ml \
	                               -package cryptokit -package secp256k1 -package bn128 -package ocaml-protoc -safe-string -thread \
	        && ocamlfind $(OCAMLC) -a -o semantics.$(LIBEXT) KRYPTO.$(EXT) msg_types.$(EXT) msg_pb.$(EXT) apiVersion.$(EXT) world.$(EXT) caching.$(EXT) BLOCKCHAIN.$(EXT) -thread \
	        && ocamlfind remove ethereum-semantics-plugin-$* \
	        && ocamlfind install ethereum-semantics-plugin-$* ../../plugin/plugin/META semantics.* *.cmi *.$(EXT)

.build/%/$(MAIN_DEFN_FILE)-kompiled/interpreter: .build/plugin-%/semantics.$(LIBEXT)
	eval $$(opam config env) \
	    && cd .build/$*/$(MAIN_DEFN_FILE)-kompiled \
	        && ocamllex lexer.mll \
	        && ocamlyacc parser.mly \
	        && ocamlfind $(OCAMLC) -c -g -package gmp -package zarith -package uuidm -safe-string prelude.ml plugin.ml parser.mli parser.ml lexer.ml hooks.ml run.ml -thread \
	        && ocamlfind $(OCAMLC) -c -g -w -11-26 -package gmp -package zarith -package uuidm -package ethereum-semantics-plugin-$* -safe-string realdef.ml -match-context-rows 2 \
	        && ocamlfind $(OCAMLC) $(LIBFLAG) -o realdef.$(DLLEXT) realdef.$(EXT) \
	        && ocamlfind $(OCAMLC) -g -o interpreter constants.$(EXT) prelude.$(EXT) plugin.$(EXT) parser.$(EXT) lexer.$(EXT) hooks.$(EXT) run.$(EXT) interpreter.ml \
	                               -package gmp -package dynlink -package zarith -package str -package uuidm -package unix -package ethereum-semantics-plugin-$* -linkpkg -linkall -thread -safe-string

# Node Backend

.build/node/$(MAIN_DEFN_FILE)-kompiled/interpreter: $(node_files) .build/plugin-node/proto/msg.pb.cc
	@echo "== kompile: $@"
	${K_BIN}/kompile --debug --main-module $(MAIN_MODULE) \
	                 --syntax-module $(SYNTAX_MODULE) .build/node/$(MAIN_DEFN_FILE).k --directory .build/node --hook-namespaces "KRYPTO BLOCKCHAIN" \
	                 --backend llvm -ccopt ${PLUGIN_SUBMODULE}/plugin-c/crypto.cpp -ccopt ${PLUGIN_SUBMODULE}/plugin-c/blockchain.cpp -ccopt ${PLUGIN_SUBMODULE}/plugin-c/world.cpp -ccopt ${BUILD_DIR}/plugin-node/proto/msg.pb.cc \
	                 -ccopt -I${BUILD_DIR}/plugin-node \
	                 -ccopt -lff -ccopt -lcryptopp -ccopt -lsecp256k1 -ccopt -lprocps -ccopt -lprotobuf -ccopt -g -ccopt -std=c++11 -ccopt -O2 \
	                 -I .build/node $(KOMPILE_OPTS)

.build/plugin-node/proto/msg.pb.cc: ${PLUGIN_SUBMODULE}/plugin/proto/msg.proto
	mkdir -p .build/plugin-node
	protoc --cpp_out=.build/plugin-node -I ${PLUGIN_SUBMODULE}/plugin ${PLUGIN_SUBMODULE}/plugin/proto/msg.proto

.build/vm/kevm-vm: .build/node/$(MAIN_DEFN_FILE)-kompiled/interpreter
	mkdir -p .build/vm
	${K_BIN}/llvm-kompile .build/node/$(MAIN_DEFN_FILE)-kompiled/definition.kore .build/node/$(MAIN_DEFN_FILE)-kompiled/dt library ${PLUGIN_SUBMODULE}/vm-c/main.cpp ${PLUGIN_SUBMODULE}/vm-c/vm.cpp -I ${PLUGIN_SUBMODULE}/plugin-c/ -I ${BUILD_DIR}/plugin-node ${PLUGIN_SUBMODULE}/plugin-c/*.cpp ${BUILD_DIR}/plugin-node/proto/msg.pb.cc -lff -lprotobuf -lgmp -lprocps -lcryptopp -lsecp256k1 -I ${PLUGIN_SUBMODULE}/vm-c/ -I ${PLUGIN_SUBMODULE}/vm-c/kevm/ ${PLUGIN_SUBMODULE}/vm-c/kevm/semantics.cpp -o .build/vm/kevm-vm -g -O2

# LLVM Backend

.build/llvm/$(MAIN_DEFN_FILE)-kompiled/interpreter: $(ocaml_files)
	@echo "== kompile: $@"
	${K_BIN}/kompile --debug --main-module $(MAIN_MODULE) \
	                 --syntax-module $(SYNTAX_MODULE) .build/ocaml/$(MAIN_DEFN_FILE).k --directory .build/llvm --hook-namespaces KRYPTO \
	                 --backend llvm -ccopt ${PLUGIN_SUBMODULE}/plugin-c/crypto.cpp \
	                 -ccopt -lff -ccopt -lcryptopp -ccopt -lsecp256k1 -ccopt -lprocps -ccopt -g -ccopt -std=c++11 -ccopt -O2 \
	                 -I .build/llvm -I .build/ocaml $(KOMPILE_OPTS)

# Tests
# -----

TEST_CONCRETE_BACKEND:=ocaml
TEST_SYMBOLIC_BACKEND:=java
TEST:=./kevm
KPROVE_MODULE:=VERIFICATION
CHECK:=git --no-pager diff --no-index --ignore-all-space

KEVM_MODE:=NORMAL
KEVM_SCHEDULE:=PETERSBURG

test-all: test-all-conformance test-all-proof test-interactive test-parse
test: test-conformance test-proof test-interactive test-parse

split-tests: tests/ethereum-tests/make.timestamp

tests/%/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init -- tests/$*
	touch $@

# Generic Test Harnesses

tests/ethereum-tests/VMTests/%: KEVM_MODE=VMTESTS
tests/ethereum-tests/VMTests/%: KEVM_SCHEDULE=DEFAULT

tests/%.run: tests/%
	MODE=$(KEVM_MODE) SCHEDULE=$(KEVM_SCHEDULE) $(TEST) interpret --backend $(TEST_CONCRETE_BACKEND) $< > tests/$*.$(TEST_CONCRETE_BACKEND)-out \
	    || $(CHECK) tests/templates/output-success-$(TEST_CONCRETE_BACKEND).json tests/$*.$(TEST_CONCRETE_BACKEND)-out
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.run-interactive: tests/%
	MODE=$(KEVM_MODE) SCHEDULE=$(KEVM_SCHEDULE) $(TEST) run --backend $(TEST_CONCRETE_BACKEND) $< > tests/$*.$(TEST_CONCRETE_BACKEND)-out \
	    || $(CHECK) tests/templates/output-success-$(TEST_CONCRETE_BACKEND).json tests/$*.$(TEST_CONCRETE_BACKEND)-out
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.parse: tests/%
	$(TEST) kast --backend $(TEST_CONCRETE_BACKEND) $< > $@-out
	$(CHECK) $@-expected $@-out
	rm -rf $@-out

tests/%.prove: tests/%
	$(TEST) prove --backend $(TEST_SYMBOLIC_BACKEND) $< --format-failures --def-module $(KPROVE_MODULE)

# Smoke Tests

smoke_tests_run=tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json \
                tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json \
                tests/interactive/sumTo10.evm

smoke_tests_prove=tests/specs/examples/sum-to-n-spec.k \
                  tests/specs/ds-token-erc20/transfer-failure-1-a-spec.k

# Conformance Tests

tests/ethereum-tests/%.json: tests/ethereum-tests/make.timestamp

test-all-conformance: test-all-vm test-all-bchain
test-slow-conformance: test-slow-vm test-slow-bchain
test-conformance: test-vm test-bchain

vm_tests=$(wildcard tests/ethereum-tests/VMTests/*/*.json)
slow_vm_tests=$(wildcard tests/ethereum-tests/VMTests/vmPerformance/*.json)
quick_vm_tests=$(filter-out $(slow_vm_tests), $(vm_tests))

test-all-vm: $(all_vm_tests:=.run)
test-slow-vm: $(slow_vm_tests:=.run)
test-vm: $(quick_vm_tests:=.run)

bchain_tests=$(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/*/*.json)
slow_bchain_tests=$(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call50000*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Return50000*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call1MB1024Calldepth_d1g0v0.json) \
                  tests/ethereum-tests/BlockchainTests/GeneralStateTests/stCreateTest/CREATE_ContractRETURNBigOffset_d2g0v0.json \
                  tests/ethereum-tests/BlockchainTests/GeneralStateTests/stCreateTest/CREATE_ContractRETURNBigOffset_d1g0v0.json
bad_bchain_tests= tests/ethereum-tests/BlockchainTests/GeneralStateTests/stCreate2/RevertOpcodeInCreateReturns_d0g0v0.json \
                  tests/ethereum-tests/BlockchainTests/GeneralStateTests/stCreate2/RevertInCreateInInit_d0g0v0.json
failing_bchain_tests=$(shell cat tests/failing.${TEST_CONCRETE_BACKEND})
all_bchain_tests=$(filter-out $(bad_bchain_tests), $(filter-out $(failing_bchain_tests), $(bchain_tests)))
quick_bchain_tests=$(filter-out $(slow_bchain_tests), $(all_bchain_tests))

test-all-bchain: $(all_bchain_tests:=.run)
test-slow-bchain: $(slow_bchain_tests:=.run)
test-bchain: $(quick_bchain_tests:=.run)

# Proof Tests

proof_specs_dir:=tests/specs
proof_tests=$(wildcard $(proof_specs_dir)/*/*-spec.k)

test-proof: $(proof_tests:=.prove)

# Parse Tests

parse_tests:=$(wildcard tests/interactive/*.json) \
             $(wildcard tests/interactive/*.evm)

test-parse: $(parse_tests:=.parse)
	echo $(parse_tests)

# Interactive Tests

test-interactive: test-interactive-run test-interactive-prove test-interactive-help

test-interactive-run: $(smoke_tests_run:=.run-interactive)
test-interactive-prove: $(smoke_tests_prove:=.prove)

test-interactive-help:
	$(TEST) help

# Media
# -----

media: sphinx media-pdf

### Media generated PDFs

media_pdfs:=201710-presentation-devcon3 201801-presentation-csf

media/%.pdf: media/%.md media/citations.md
	@echo "== media: $@"
	mkdir -p $(dir $@)
	cat $^ | pandoc --from markdown --filter pandoc-citeproc --to beamer --output $@
	@echo "== $*: presentation generated at $@"

media-pdf: $(patsubst %, media/%.pdf, $(media_pdfs))

metropolis-theme: $(BUILD_DIR)/media/metropolis/beamerthememetropolis.sty

$(BUILD_DIR)/media/metropolis/beamerthememetropolis.sty:
	@echo "== submodule: $@"
	git submodule update --init -- $(dir $@)
	cd $(dir $@) && make

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
