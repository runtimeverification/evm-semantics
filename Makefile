# Settings
# --------

BUILD_DIR:=.build
DEFN_DIR:=$(BUILD_DIR)/defn
BUILD_LOCAL:=$(CURDIR)/$(BUILD_DIR)/local
LIBRARY_PATH:=$(BUILD_LOCAL)/lib
C_INCLUDE_PATH:=$(BUILD_LOCAL)/include
CPLUS_INCLUDE_PATH:=$(BUILD_LOCAL)/include
PKG_CONFIG_PATH:=$(LIBRARY_PATH)/pkgconfig
export LIBRARY_PATH
export C_INCLUDE_PATH
export CPLUS_INCLUDE_PATH
export PKG_CONFIG_PATH

INSTALL_PREFIX:=/usr/local
INSTALL_DIR?=$(DESTDIR)$(INSTALL_PREFIX)/bin

DEPS_DIR:=deps
K_SUBMODULE:=$(abspath $(DEPS_DIR)/k)
PLUGIN_SUBMODULE:=$(abspath $(DEPS_DIR)/plugin)

K_RELEASE:=$(K_SUBMODULE)/k-distribution/target/release/k
K_BIN:=$(K_RELEASE)/bin
K_LIB:=$(K_RELEASE)/lib

PATH:=$(K_BIN):$(PATH)
export PATH

# need relative path for `pandoc` on MacOS
PANDOC_TANGLE_SUBMODULE:=$(DEPS_DIR)/pandoc-tangle
TANGLER:=$(PANDOC_TANGLE_SUBMODULE)/tangle.lua
LUA_PATH:=$(PANDOC_TANGLE_SUBMODULE)/?.lua;;
export TANGLER
export LUA_PATH

.PHONY: all clean clean-submodules distclean install uninstall \
        deps all-deps llvm-deps haskell-deps repo-deps system-deps k-deps ocaml-deps plugin-deps libsecp256k1 libff \
        build build-ocaml build-java build-node build-kore split-tests \
        defn java-defn ocaml-defn node-defn haskell-defn llvm-defn \
        test test-all test-conformance test-slow-conformance test-all-conformance \
        test-vm test-slow-vm test-all-vm test-bchain test-slow-bchain test-all-bchain \
        test-prove test-klab-prove test-parse test-failure \
        test-interactive test-interactive-help test-interactive-run test-interactive-prove test-interactive-search test-interactive-firefly \
        media media-pdf sphinx metropolis-theme
.SECONDARY:

all: build split-tests

clean:
	rm -rf $(DEFN_DIR)
	git clean -dfx -- tests/specs

distclean: clean
	rm -rf $(BUILD_DIR)

clean-submodules: distclean
	rm -rf $(DEPS_DIR)/k/make.timestamp $(DEPS_DIR)/metropolis/*.sty \
	       tests/ethereum-tests/make.timestamp $(DEPS_DIR)/plugin/make.timestamp  \
	       $(DEPS_DIR)/libff/build
	cd $(DEPS_DIR)/k         && mvn clean --quiet
	cd $(DEPS_DIR)/secp256k1 && make distclean || true

# Non-K Dependencies
# ------------------

libsecp256k1_out:=$(LIBRARY_PATH)/pkgconfig/libsecp256k1.pc
libff_out:=$(LIBRARY_PATH)/libff.a

libsecp256k1: $(libsecp256k1_out)
libff: $(libff_out)

$(DEPS_DIR)/secp256k1/autogen.sh:
	@echo "== submodule: $(DEPS_DIR)/secp256k1"
	git submodule update --init --recursive -- $(DEPS_DIR)/secp256k1

$(libsecp256k1_out): $(DEPS_DIR)/secp256k1/autogen.sh
	cd $(DEPS_DIR)/secp256k1/ \
	    && ./autogen.sh \
	    && ./configure --enable-module-recovery --prefix="$(BUILD_LOCAL)" \
	    && make -s -j4 \
	    && make install

UNAME_S := $(shell uname -s)

ifeq ($(UNAME_S),Linux)
  LIBFF_CMAKE_FLAGS=
  LINK_PROCPS=-lprocps
else
  LIBFF_CMAKE_FLAGS=-DWITH_PROCPS=OFF
  LINK_PROCPS=
endif

LIBFF_CC ?=clang-8
LIBFF_CXX?=clang++-8

$(DEPS_DIR)/libff/CMakeLists.txt:
	@echo "== submodule: $(DEPS_DIR)/libff"
	git submodule update --init --recursive -- $(DEPS_DIR)/libff

$(libff_out): $(DEPS_DIR)/libff/CMakeLists.txt
	cd $(DEPS_DIR)/libff/ \
	    && mkdir -p build \
	    && cd build \
	    && CC=$(LIBFF_CC) CXX=$(LIBFF_CXX) cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(BUILD_LOCAL) $(LIBFF_CMAKE_FLAGS) \
	    && make -s -j4 \
	    && make install

# K Dependencies
# --------------

all-deps: deps llvm-deps haskell-deps
all-deps: BACKEND_SKIP=
llvm-deps: $(libff_out) deps
llvm-deps: BACKEND_SKIP=-Dhaskell.backend.skip
haskell-deps: deps
haskell-deps: BACKEND_SKIP=-Dllvm.backend.skip

deps: repo-deps system-deps
repo-deps: tangle-deps k-deps plugin-deps
system-deps: ocaml-deps
k-deps: $(K_SUBMODULE)/make.timestamp
tangle-deps: $(TANGLER)
plugin-deps: $(PLUGIN_SUBMODULE)/make.timestamp

BACKEND_SKIP=-Dhaskell.backend.skip -Dllvm.backend.skip

$(K_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init --recursive -- $(K_SUBMODULE)
	cd $(K_SUBMODULE) && mvn package -DskipTests -U $(BACKEND_SKIP)
	touch $(K_SUBMODULE)/make.timestamp

$(TANGLER):
	@echo "== submodule: $@"
	git submodule update --init -- $(PANDOC_TANGLE_SUBMODULE)

$(PLUGIN_SUBMODULE)/make.timestamp:
	@echo "== submodule: $@"
	git submodule update --init --recursive -- $(PLUGIN_SUBMODULE)
	touch $(PLUGIN_SUBMODULE)/make.timestamp

ocaml-deps:
	eval $$(opam config env) \
	    opam install --yes mlgmp zarith uuidm cryptokit secp256k1.0.3.2 bn128 ocaml-protoc rlp yojson hex ocp-ocamlres

# Building
# --------

MAIN_MODULE:=ETHEREUM-SIMULATION
SYNTAX_MODULE:=$(MAIN_MODULE)
MAIN_DEFN_FILE:=driver
KOMPILE_OPTS:=
LLVM_KOMPILE_OPTS:=

ocaml_kompiled:=$(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled/interpreter
java_kompiled:=$(DEFN_DIR)/java/$(MAIN_DEFN_FILE)-kompiled/timestamp
node_kompiled:=$(DEFN_DIR)/vm/kevm-vm
haskell_kompiled:=$(DEFN_DIR)/haskell/$(MAIN_DEFN_FILE)-kompiled/definition.kore
llvm_kompiled:=$(DEFN_DIR)/llvm/$(MAIN_DEFN_FILE)-kompiled/interpreter

build: build-ocaml build-java
build-ocaml: $(ocaml_kompiled)
build-java: $(java_kompiled)
build-node: $(node_kompiled)
build-haskell: $(haskell_kompiled)
build-llvm: $(llvm_kompiled)

# Tangle definition from *.md files

concrete_tangle:=.k:not(.node):not(.symbolic),.standalone,.concrete
symbolic_tangle:=.k:not(.node):not(.concrete),.standalone,.symbolic
node_tangle:=.k:not(.standalone):not(.symbolic),.node,.concrete

k_files=driver.k data.k network.k evm.k krypto.k edsl.k evm-node.k
EXTRA_K_FILES+=$(MAIN_DEFN_FILE).k
ALL_K_FILES:=$(k_files) $(EXTRA_K_FILES)

ocaml_files=$(patsubst %, $(DEFN_DIR)/ocaml/%, $(ALL_K_FILES))
llvm_files=$(patsubst %, $(DEFN_DIR)/llvm/%, $(ALL_K_FILES))
java_files=$(patsubst %, $(DEFN_DIR)/java/%, $(ALL_K_FILES))
haskell_files=$(patsubst %, $(DEFN_DIR)/haskell/%, $(ALL_K_FILES))
node_files=$(patsubst %, $(DEFN_DIR)/node/%, $(ALL_K_FILES))
defn_files=$(ocaml_files) $(llvm_file) $(java_files) $(haskell_files) $(node_files)

defn: $(defn_files)
ocaml-defn: $(ocaml_files)
llvm-defn: $(llvm_files)
java-defn: $(java_files)
haskell-defn: $(haskell_files)
node-defn: $(node_files)

$(DEFN_DIR)/ocaml/%.k: %.md $(TANGLER)
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(concrete_tangle)" $< > $@

$(DEFN_DIR)/llvm/%.k: %.md $(TANGLER)
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(concrete_tangle)" $< > $@

$(DEFN_DIR)/java/%.k: %.md $(TANGLER)
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(symbolic_tangle)" $< > $@

$(DEFN_DIR)/haskell/%.k: %.md $(TANGLER)
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(symbolic_tangle)" $< > $@

$(DEFN_DIR)/node/%.k: %.md $(TANGLER)
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(TANGLER)" --metadata=code:"$(node_tangle)" $< > $@

# Java Backend

$(java_kompiled): $(java_files)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend java \
	                 --syntax-module $(SYNTAX_MODULE) $(DEFN_DIR)/java/$(MAIN_DEFN_FILE).k \
	                 --directory $(DEFN_DIR)/java -I $(DEFN_DIR)/java \
	                 $(KOMPILE_OPTS)

# Haskell Backend

$(haskell_kompiled): $(haskell_files)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend haskell --hook-namespaces KRYPTO \
	                 --syntax-module $(SYNTAX_MODULE) $(DEFN_DIR)/haskell/$(MAIN_DEFN_FILE).k \
	                 --directory $(DEFN_DIR)/haskell -I $(DEFN_DIR)/haskell \
	                 $(KOMPILE_OPTS)

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

$(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled/constants.$(EXT): $(ocaml_files)
	@echo "== kompile: $@"
	eval $$(opam config env) \
	    && $(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) \
	                        --syntax-module $(SYNTAX_MODULE) $(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE).k \
	                        --hook-namespaces "KRYPTO" --gen-ml-only -O3 --non-strict \
	                        --directory $(DEFN_DIR)/ocaml -I $(DEFN_DIR)/ocaml $(KOMPILE_OPTS) \
	    && cd $(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled \
	    && ocamlfind $(OCAMLC) -c -g constants.ml -package gmp -package zarith -safe-string

$(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled/plugin/semantics.$(LIBEXT): $(wildcard $(PLUGIN_SUBMODULE)/plugin/*.ml $(PLUGIN_SUBMODULE)/plugin/*.mli) $(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled/constants.$(EXT)
	mkdir -p $(dir $@)
	cp $(PLUGIN_SUBMODULE)/plugin/*.ml $(PLUGIN_SUBMODULE)/plugin/*.mli $(dir $@)
	eval $$(opam config env) \
	    && ocp-ocamlres -format ocaml $(PLUGIN_SUBMODULE)/plugin/proto/VERSION -o $(dir $@)/apiVersion.ml \
	    && ocaml-protoc $(PLUGIN_SUBMODULE)/plugin/proto/*.proto -ml_out $(dir $@) \
	    && cd $(dir $@) \
	        && ocamlfind $(OCAMLC) -c -g -I $(CURDIR)/$(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled \
	                               KRYPTO.ml \
	                               -package cryptokit -package secp256k1 -package bn128 -package ocaml-protoc -safe-string -thread \
	        && ocamlfind $(OCAMLC) -a -o semantics.$(LIBEXT) KRYPTO.$(EXT) -thread \
	        && ocamlfind remove ethereum-semantics-plugin-ocaml \
	        && ocamlfind install ethereum-semantics-plugin-ocaml $(PLUGIN_SUBMODULE)/plugin/META semantics.* *.cmi *.$(EXT)

$(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled/interpreter: $(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled/plugin/semantics.$(LIBEXT)
	eval $$(opam config env) \
	    && cd $(DEFN_DIR)/ocaml/$(MAIN_DEFN_FILE)-kompiled \
	        && ocamllex lexer.mll \
	        && ocamlyacc parser.mly \
	        && ocamlfind $(OCAMLC) -c -g -package gmp -package zarith -package uuidm -safe-string prelude.ml plugin.ml parser.mli parser.ml lexer.ml hooks.ml run.ml -thread \
	        && ocamlfind $(OCAMLC) -c -g -w -11-26 -package gmp -package zarith -package uuidm -package ethereum-semantics-plugin-ocaml -safe-string realdef.ml -match-context-rows 2 \
	        && ocamlfind $(OCAMLC) $(LIBFLAG) -o realdef.$(DLLEXT) realdef.$(EXT) \
	        && ocamlfind $(OCAMLC) -g -o interpreter constants.$(EXT) prelude.$(EXT) plugin.$(EXT) parser.$(EXT) lexer.$(EXT) hooks.$(EXT) run.$(EXT) interpreter.ml \
	                               -package gmp -package dynlink -package zarith -package str -package uuidm -package unix -package ethereum-semantics-plugin-ocaml -linkpkg -linkall -thread -safe-string

# Node Backend

$(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/interpreter: $(node_files) $(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/plugin/proto/msg.pb.cc $(libff_out)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend llvm \
	                 --syntax-module $(SYNTAX_MODULE) $(DEFN_DIR)/node/$(MAIN_DEFN_FILE).k \
	                 --directory $(DEFN_DIR)/node -I $(DEFN_DIR)/node -I $(DEFN_DIR)/node \
	                 --hook-namespaces "KRYPTO BLOCKCHAIN" \
			 --iterated \
	                 $(KOMPILE_OPTS) \
	                 -ccopt $(PLUGIN_SUBMODULE)/plugin-c/crypto.cpp -ccopt $(PLUGIN_SUBMODULE)/plugin-c/blockchain.cpp -ccopt $(PLUGIN_SUBMODULE)/plugin-c/world.cpp -ccopt $(CURDIR)/$(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/plugin/proto/msg.pb.cc \
	                 -ccopt -I$(CURDIR)/$(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/plugin \
	                 -ccopt -L$(LIBRARY_PATH) \
	                 -ccopt -lff -ccopt -lcryptopp -ccopt -lsecp256k1 $(addprefix -ccopt ,$(LINK_PROCPS)) -ccopt -lprotobuf -ccopt -g -ccopt -std=c++11 -ccopt -O2

$(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/plugin/proto/msg.pb.cc: $(PLUGIN_SUBMODULE)/plugin/proto/msg.proto
	mkdir -p $(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/plugin
	protoc --cpp_out=$(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/plugin -I $(PLUGIN_SUBMODULE)/plugin $(PLUGIN_SUBMODULE)/plugin/proto/msg.proto

$(node_kompiled): $(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/interpreter $(libff_out)
	mkdir -p $(DEFN_DIR)/vm
	$(K_BIN)/llvm-kompile $(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/definition.kore $(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/dt library $(PLUGIN_SUBMODULE)/vm-c/main.cpp $(PLUGIN_SUBMODULE)/vm-c/vm.cpp \
	                      $(PLUGIN_SUBMODULE)/plugin-c/*.cpp $(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/plugin/proto/msg.pb.cc $(PLUGIN_SUBMODULE)/vm-c/kevm/semantics.cpp -o $@ -g -O2 \
	                      -I $(PLUGIN_SUBMODULE)/plugin-c/ -I $(DEFN_DIR)/node/$(MAIN_DEFN_FILE)-kompiled/plugin -I $(PLUGIN_SUBMODULE)/vm-c/ -I $(PLUGIN_SUBMODULE)/vm-c/kevm/ -I node/ \
	                      $(LLVM_KOMPILE_OPTS) \
	                      -L$(LIBRARY_PATH) \
	                      -lff -lprotobuf -lgmp $(LINK_PROCPS) -lcryptopp -lsecp256k1

# LLVM Backend

$(llvm_kompiled): $(llvm_files) $(libff_out)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module $(MAIN_MODULE) --backend llvm \
	                 --syntax-module $(SYNTAX_MODULE) $(DEFN_DIR)/llvm/$(MAIN_DEFN_FILE).k \
	                 --directory $(DEFN_DIR)/llvm -I $(DEFN_DIR)/llvm -I $(DEFN_DIR)/llvm \
	                 --hook-namespaces KRYPTO \
	                 $(KOMPILE_OPTS) \
	                 -ccopt $(PLUGIN_SUBMODULE)/plugin-c/crypto.cpp \
	                 -ccopt -g -ccopt -std=c++11 -ccopt -O2 \
	                 -ccopt -L$(LIBRARY_PATH) \
	                 -ccopt -lff -ccopt -lcryptopp -ccopt -lsecp256k1 $(addprefix -ccopt ,$(LINK_PROCPS))

# Installing
# ----------

KEVM_RELEASE_TAG?=

install: $(INSTALL_DIR)/$(notdir $(node_kompiled))
$(INSTALL_DIR)/$(notdir $(node_kompiled)): $(node_kompiled)
	mkdir -p $(INSTALL_DIR)
	cp $(node_kompiled) $(INSTALL_DIR)/

uninstall:
	rm $(INSTALL_DIR)/$(notdir $(node_kompiled))

release.md: INSTALL.md
	echo "KEVM Release $(KEVM_RELEASE_TAG)"  > $@
	echo                                    >> $@
	cat INSTALL.md                          >> $@

# Tests
# -----

TEST_CONCRETE_BACKEND:=ocaml
TEST_SYMBOLIC_BACKEND:=java
TEST:=./kevm
KPROVE_MODULE:=VERIFICATION
CHECK:=git --no-pager diff --no-index --ignore-all-space

KEVM_MODE:=NORMAL
KEVM_SCHEDULE:=PETERSBURG

test-all: test-all-conformance test-prove test-interactive test-parse
test: test-conformance test-prove test-interactive test-parse

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

tests/%.run-expected: tests/% tests/%.expected
	MODE=$(KEVM_MODE) SCHEDULE=$(KEVM_SCHEDULE) $(TEST) run --backend $(TEST_CONCRETE_BACKEND) $< > tests/$*.$(TEST_CONCRETE_BACKEND)-out \
	    || $(CHECK) tests/$*.expected tests/$*.$(TEST_CONCRETE_BACKEND)-out
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.parse: tests/%
	$(TEST) kast --backend $(TEST_CONCRETE_BACKEND) $< kast > $@-out
	$(CHECK) $@-expected $@-out
	rm -rf $@-out

tests/%.prove: tests/%
	$(TEST) prove --backend $(TEST_SYMBOLIC_BACKEND) $< --format-failures --def-module $(KPROVE_MODULE)

tests/%.search: tests/%
	$(TEST) search --backend $(TEST_SYMBOLIC_BACKEND) $< "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" > $@-out
	$(CHECK) $@-expected $@-out
	rm -rf $@-out

tests/%.klab-prove: tests/%
	$(TEST) klab-prove --backend $(TEST_SYMBOLIC_BACKEND) $< --format-failures --def-module $(KPROVE_MODULE)

# Smoke Tests

smoke_tests_run=tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json \
                tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json \
                tests/interactive/sumTo10.evm

smoke_tests_prove=tests/specs/ds-token-erc20/transfer-failure-1-a-spec.k

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
failing_bchain_tests=$(shell cat tests/failing.$(TEST_CONCRETE_BACKEND))
all_bchain_tests=$(filter-out $(bad_bchain_tests), $(filter-out $(failing_bchain_tests), $(bchain_tests)))
quick_bchain_tests=$(filter-out $(slow_bchain_tests), $(all_bchain_tests))

test-all-bchain: $(all_bchain_tests:=.run)
test-slow-bchain: $(slow_bchain_tests:=.run)
test-bchain: $(quick_bchain_tests:=.run)

# Proof Tests

prove_specs_dir:=tests/specs
prove_tests=$(wildcard $(prove_specs_dir)/*/*-spec.k)

test-prove: $(prove_tests:=.prove)
test-klab-prove: $(smoke_tests_prove:=.klab-prove)

# Parse Tests

parse_tests:=$(wildcard tests/interactive/*.json) \
             $(wildcard tests/interactive/*.evm)

test-parse: $(parse_tests:=.parse)
	echo $(parse_tests)

# Failing correctly tests

failure_tests:=$(wildcard tests/failing/*.json)

test-failure: $(failure_tests:=.run-expected)

# Interactive Tests

test-interactive: test-interactive-run test-interactive-prove test-interactive-search test-interactive-help

test-interactive-run: $(smoke_tests_run:=.run-interactive)
test-interactive-prove: $(smoke_tests_prove:=.prove)

search_tests:=$(wildcard tests/interactive/search/*.evm)
test-interactive-search: $(search_tests:=.search)

test-interactive-help:
	$(TEST) help

# Notice that `npm install` comes after `npx kevm-ganache-cli` to allow time for it to start up.
test-interactive-firefly:
	mkdir -p $(BUILD_DIR)/firefly
	cd $(BUILD_DIR)/firefly                                                  \
	    && rm -rf openzeppelin-solidity                                      \
	    && git clone 'https://github.com/openzeppelin/openzeppelin-solidity' \
	    && cd openzeppelin-solidity                                          \
	    && git checkout b8c8308                                              \
	    && { npx kevm-ganache-cli --gasLimit 0xfffffffffff --port 8545 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501200,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501201,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501202,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501203,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501204,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501205,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501206,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501207,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501208,1000000000000000000000000 --account=0x2bdd21761a483f71054e14f5b827213567971c676928d9a1808cbfa4b7501209,1000000000000000000000000 & }                                        \
	    && npm install                                                       \
	    && npx truffle test

# Media
# -----

media: sphinx media-pdf

### Media generated PDFs

media_pdfs := 201710-presentation-devcon3                          \
              201801-presentation-csf                              \
              201905-exercise-k-workshop                           \
              201908-trufflecon-workshop 201908-trufflecon-firefly

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
SPHINXBUILDDIR = $(BUILD_DIR)/sphinx-docs

# Internal variables.
PAPEROPT_a4     = -D latex_paper_size=a4
PAPEROPT_letter = -D latex_paper_size=letter
ALLSPHINXOPTS   = -d ../$(SPHINXBUILDDIR)/doctrees $(PAPEROPT_$(PAPER)) $(SPHINXOPTS) .
# the i18n builder cannot share the environment and doctrees with the others
I18NSPHINXOPTS  = $(PAPEROPT_$(PAPER)) $(SPHINXOPTS) .

sphinx:
	@echo "== media: $@"
	mkdir -p $(SPHINXBUILDDIR) \
	    && cp -r media/sphinx-docs/* $(SPHINXBUILDDIR) \
	    && cp -r *.md $(SPHINXBUILDDIR)/. \
	    && cd $(SPHINXBUILDDIR) \
	    && sed -i 's/{.k[ a-zA-Z.-]*}/k/g' *.md \
	    && $(SPHINXBUILD) -b dirhtml $(ALLSPHINXOPTS) html \
	    && $(SPHINXBUILD) -b text $(ALLSPHINXOPTS) html/text
	@echo "== sphinx: HTML generated in $(SPHINXBUILDDIR)/html, text in $(SPHINXBUILDDIR)/html/text"
