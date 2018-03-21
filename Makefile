# Settings
# --------

BUILD_DIR:=$(CURDIR)/.build
K_SUBMODULE:=$(BUILD_DIR)/k
PANDOC_TANGLE_SUBMODULE:=$(BUILD_DIR)/pandoc-tangle
PLUGIN_SUBMODULE:=plugin
BUILD_LOCAL:=$(BUILD_DIR)/local

PKG_CONFIG_PATH:=$(BUILD_LOCAL)/lib/pkgconfig
export PKG_CONFIG_PATH

TANGLER:=$(PANDOC_TANGLE_SUBMODULE)/tangle.lua
LUA_PATH:=$(PANDOC_TANGLE_SUBMODULE)/?.lua;;
export TANGLER
export LUA_PATH

.PHONY: all clean deps k-deps tangle-deps ocaml-deps plugin-deps build build-ocaml build-java build-node defn sphinx split-tests \
		test test-all test-concrete test-all-concrete test-conformance test-slow-conformance test-all-conformance \
		test-vm test-slow-vm test-all-vm test-bchain test-slow-bchain test-all-bchain \
		test-proof test-interactive
.SECONDARY:

all: build split-tests

clean: clean-submodules
	rm -rf .build/java .build/plugin-ocaml .build/plugin-node .build/ocaml .build/node .build/logs .build/local .build/vm tests/proofs/specs

clean-submodules:
	rm -rf .build/k/make.timestamp .build/pandoc-tangle/make.timestamp tests/ethereum-tests/make.timestamp tests/proofs/make.timestamp plugin/make.timestamp

distclean: clean
	opam switch system
	opam switch remove 4.03.0+k --yes || true
	cd $(K_SUBMODULE) \
		&& mvn clean -q
	git submodule deinit --force -- ./

# Dependencies
# ------------

deps: k-deps tangle-deps ocaml-deps plugin-deps
k-deps: $(K_SUBMODULE)/make.timestamp
tangle-deps: $(PANDOC_TANGLE_SUBMODULE)/make.timestamp
plugin-deps: $(PLUGIN_SUBMODULE)/make.timestamp

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

$(PLUGIN_SUBMODULE)/make.timestamp: ocaml-deps
	@echo "== submodule: $@"
	git submodule update --init --recursive -- $(PLUGIN_SUBMODULE)
	touch $(PLUGIN_SUBMODULE)/make.timestamp

ocaml-deps: .build/local/lib/pkgconfig/libsecp256k1.pc
	opam init --quiet --no-setup
	opam repository add k "$(K_SUBMODULE)/k-distribution/target/release/k/lib/opam" \
		|| opam repository set-url k "$(K_SUBMODULE)/k-distribution/target/release/k/lib/opam"
	opam update
	opam switch 4.03.0+k
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

# Tangle definition from *.md files

standalone_tangle:=.k:not(.node),.standalone
node_tangle:=.k:not(.standalone),.node

k_files:=driver.k data.k network.k evm.k analysis.k krypto.k edsl.k evm-node.k
ocaml_files:=$(patsubst %,.build/ocaml/%,$(k_files))
java_files:=$(patsubst %,.build/java/%,$(k_files))
node_files:=$(patsubst %,.build/node/%,$(k_files))
defn_files:=$(ocaml_files) $(java_files) $(node_files)

defn: $(defn_files)

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

# Java Backend

.build/java/driver-kompiled/timestamp: $(java_files)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module ETHEREUM-SIMULATION --backend java \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/java -I .build/java

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

.build/%/driver-kompiled/constants.$(EXT): $(defn_files)
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
			&& ocamlfind $(OCAMLC) -c -g -I ../$*/driver-kompiled msg_types.mli msg_types.ml msg_pb.mli msg_pb.ml threadLocal.mli threadLocal.ml apiVersion.ml world.mli world.ml caching.mli caching.ml BLOCKCHAIN.ml KRYPTO.ml \
								   -package cryptokit -package secp256k1 -package bn128 -package ocaml-protoc -safe-string -thread \
			&& ocamlfind $(OCAMLC) -a -o semantics.$(LIBEXT) KRYPTO.$(EXT) msg_types.$(EXT) msg_pb.$(EXT) threadLocal.$(EXT) apiVersion.$(EXT) world.$(EXT) caching.$(EXT) BLOCKCHAIN.$(EXT) -thread \
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
TEST=./kevm test

test-all: test-all-concrete test-all-proof
test: test-concrete test-proof

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
quick_vm_tests=$(filter-out $(slow_vm_tests), $(vm_tests))

test-all-vm: $(vm_tests:=.test)
test-slow-vm: $(slow_vm_tests:=.test)
test-vm: $(quick_vm_tests:=.test)

tests/ethereum-tests/VMTests/%.test: tests/ethereum-tests/VMTests/% build
	MODE=VMTESTS $(TEST) $< tests/templates/output-success.txt

# BlockchainTests

bchain_tests=$(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/*/*.json)
slow_bchain_tests=$(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call50000*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Return50000*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call1MB1024Calldepth_d1g0v0.json)
                  # $(wildcard tests/BlockchainTests/GeneralStateTests/*/*/*_Constantinople.json)
quick_bchain_tests=$(filter-out $(slow_bchain_tests), $(bchain_tests))

test-all-bchain: $(bchain_tests:=.test)
test-slow-bchain: $(bchain_tests:=.test)
test-bchain: $(quick_bchain_tests:=.test)

tests/ethereum-tests/BlockchainTests/%.test: tests/ethereum-tests/BlockchainTests/% build
	$(TEST) $< tests/templates/output-success.txt

# InteractiveTests

interactive_tests:=$(wildcard tests/interactive/*.json) \
                   $(wildcard tests/interactive/*/*.evm)

test-interactive: $(interactive_tests:=.test)

tests/interactive/%.json.test: tests/interactive/%.json tests/interactive/%.json.out build
	$(TEST) $< $<.out

tests/interactive/gas-analysis/%.evm.test: tests/interactive/gas-analysis/%.evm tests/interactive/gas-analysis/%.evm.out build
	MODE=GASANALYZE $(TEST) $< $<.out

# ProofTests

proof_dir:=tests/proofs/specs
proof_tests=$(wildcard $(proof_dir)/*/*-spec.k)

test-proof: $(proof_tests:=.test)

$(proof_dir)/%.test: $(proof_dir)/% build-java
	$(TEST) $< tests/templates/proof-success.txt

split-proof-tests: tests/proofs/make.timestamp
	$(MAKE) -C tests/proofs $@

# Sphinx HTML Documentation
# -------------------------

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
	mkdir $(SPHINXBUILDDIR) \
		&& cp -r *.md proofs $(SPHINXBUILDDIR)/. \
		&& cd $(SPHINXBUILDDIR) \
		&& pandoc --from markdown --to rst README.md --output index.rst \
		&& sed -i 's/{.k[ a-zA-Z.-]*}/k/g' *.md proofs/*.md \
		&& $(SPHINXBUILD) -b dirhtml $(ALLSPHINXOPTS) html \
		&& $(SPHINXBUILD) -b text $(ALLSPHINXOPTS) html/text \
		&& echo "[+] HTML generated in $(SPHINXBUILDDIR)/html, text in $(SPHINXBUILDDIR)/html/text"
