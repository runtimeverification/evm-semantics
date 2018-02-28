# Common to all versions of K
# ===========================

.PHONY: all clean deps k-deps tangle-deps ocaml-deps build defn sphinx split-tests \
		test test-all vm-test vm-test-all bchain-test bchain-test-all proof-test proof-test-all

all: build split-tests

clean:
	rm -rf .build/java .build/ocaml .build/node .build/logs tests/proofs .build/k/make.timestamp .build/pandoc-tangle/make.timestamp .build/local

build: .build/ocaml/driver-kompiled/interpreter .build/java/driver-kompiled/timestamp

# Dependencies
# ------------

BUILD_DIR:=$(CURDIR)/.build
K_SUBMODULE:=$(BUILD_DIR)/k
PANDOC_TANGLE_SUBMODULE:=$(BUILD_DIR)/pandoc-tangle
BUILD_LOCAL:=$(BUILD_DIR)/local

PKG_CONFIG_PATH:=$(BUILD_LOCAL)/lib/pkgconfig
export PKG_CONFIG_PATH

deps: k-deps tangle-deps ocaml-deps
k-deps: $(K_SUBMODULE)/make.timestamp
tangle-deps: $(PANDOC_TANGLE_SUBMODULE)/make.timestamp

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

ocaml-deps: .build/local/lib/pkgconfig/libsecp256k1.pc
	opam init --quiet --no-setup
	opam repository add k "$(K_SUBMODULE)/k-distribution/target/release/k/lib/opam" \
		|| opam repository set-url k "$(K_SUBMODULE)/k-distribution/target/release/k/lib/opam"
	opam update
	opam switch 4.03.0+k
	eval $$(opam config env) \
	opam install --yes mlgmp zarith uuidm cryptokit secp256k1.0.3.2 bn128

# install secp256k1 from bitcoin-core
.build/local/lib/pkgconfig/libsecp256k1.pc:
	git submodule update --init -- .build/secp256k1/
	cd .build/secp256k1/ \
		&& ./autogen.sh \
		&& ./configure --enable-module-recovery --prefix="$(BUILD_LOCAL)" \
		&& make -s -j4 \
		&& make install

K_BIN=$(K_SUBMODULE)/k-distribution/target/release/k/bin

# Building
# --------

# Tangle definition from *.md files

tangler:=$(PANDOC_TANGLE_SUBMODULE)/tangle.lua
java_tangle:=.k:not(.ocaml,.node),.java
ocaml_tangle:=.k:not(.java,.node),.ocaml
node_tangle:=.k:not(.java,.ocaml),.node

k_files:=driver.k data.k evm.k analysis.k krypto.k verification.k
ocaml_files:=$(patsubst %,.build/ocaml/%,$(k_files))
java_files:=$(patsubst %,.build/java/%,$(k_files))
node_files:=$(patsubst %,.build/node/%,$(k_files))
defn_files:=$(ocaml_files) $(java_files) $(node_files)

LUA_PATH:=$(PANDOC_TANGLE_SUBMODULE)/?.lua;;
export LUA_PATH

defn: $(defn_files)

.build/java/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(tangler)" --metadata=code:"$(java_tangle)" $< > $@

.build/ocaml/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(tangler)" --metadata=code:"$(ocaml_tangle)" $< > $@

.build/node/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(tangler)" --metadata=code:"$(node_tangle)" $< > $@

# Java Backend

.build/java/driver-kompiled/timestamp: $(java_files)
	@echo "== kompile: $@"
	$(K_BIN)/kompile --debug --main-module ETHEREUM-SIMULATION --backend java \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/java

# OCAML Backend

.build/ocaml/driver-kompiled/interpreter: $(ocaml_files) KRYPTO.ml
	@echo "== kompile: $@"
	eval $$(opam config env) \
		&& $(K_BIN)/kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/ocaml \
					--hook-namespaces KRYPTO --gen-ml-only -O3 --non-strict \
		&& ocamlfind opt -c .build/ocaml/driver-kompiled/constants.ml -package gmp -package zarith \
		&& ocamlfind opt -c -I .build/ocaml/driver-kompiled KRYPTO.ml -package cryptokit -package secp256k1 -package bn128 \
		&& ocamlfind opt -a -o semantics.cmxa KRYPTO.cmx \
		&& ocamlfind remove ethereum-semantics-plugin \
		&& ocamlfind install ethereum-semantics-plugin META semantics.cmxa semantics.a KRYPTO.cmi KRYPTO.cmx \
		&& $(K_BIN)/kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/ocaml \
					--hook-namespaces KRYPTO --packages ethereum-semantics-plugin -O3 --non-strict \
		&& cd .build/ocaml/driver-kompiled \
		&& ocamlfind opt -package gmp -package dynlink -package zarith -package str -package uuidm -package unix -package ethereum-semantics-plugin \
					     -linkpkg -inline 20 -nodynlink -O3 -linkall \
					     -o interpreter constants.cmx prelude.cmx plugin.cmx parser.cmx lexer.cmx run.cmx interpreter.ml

# Tests
# -----

# Override this with `make TEST=echo` to list tests instead of running
TEST=./kevm test

test-all: vm-test-all bchain-test-all proof-test-all interactive-test-all
test: vm-test bchain-test proof-test interactive-test

split-tests: tests/ethereum-tests/make.timestamp split-proof-tests

tests/ethereum-tests/make.timestamp:
	@echo "==  git submodule: cloning upstreams test repository"
	git submodule update --init -- tests/ethereum-tests
	touch $@

tests/ethereum-tests/%.json: tests/ethereum-tests/make.timestamp

# VMTests

vm_tests=$(wildcard tests/ethereum-tests/VMTests/*/*.json)
slow_vm_tests=$(wildcard tests/ethereum-tests/VMTests/vmPerformance/*.json)
quick_vm_tests=$(filter-out $(slow_vm_tests), $(vm_tests))

vm-test-all: $(vm_tests:=.test)
vm-test: $(quick_vm_tests:=.test)

tests/ethereum-tests/VMTests/%.test: tests/ethereum-tests/VMTests/% build
	$(TEST) $<

# BlockchainTests

bchain_tests=$(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/*/*.json)
slow_bchain_tests=$(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call50000*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Return50000*.json) \
                  $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call1MB1024Calldepth_d1g0v0.json)
                  # $(wildcard tests/BlockchainTests/GeneralStateTests/*/*/*_Constantinople.json)
quick_bchain_tests=$(filter-out $(slow_bchain_tests), $(bchain_tests))

bchain-test-all: $(bchain_tests:=.test)
bchain-test: $(quick_bchain_tests:=.test)

tests/ethereum-tests/BlockchainTests/%.test: tests/ethereum-tests/BlockchainTests/% build
	$(TEST) $<

# ProofTests

erc20_files:=totalSupply-spec.k \
             balanceOf-spec.k \
             allowance-spec.k \
             approve-spec.k \
             transfer-success-1-spec.k \
             transfer-success-2-spec.k \
             transfer-failure-1-spec.k \
             transfer-failure-2-spec.k \
             transferFrom-success-1-spec.k \
             transferFrom-success-2-spec.k \
             transferFrom-failure-1-spec.k \
             transferFrom-failure-2-spec.k

hobby_erc20_files:=totalSupply-spec.k \
                   balanceOf-spec.k \
                   allowance-spec.k \
                   approve-success-spec.k \
                   approve-failure-spec.k \
                   transfer-success-1-spec.k \
                   transfer-success-2-spec.k \
                   transfer-failure-1-spec.k \
                   transfer-failure-2-spec.k \
                   transferFrom-success-1-spec.k \
                   transferFrom-success-2-spec.k \
                   transferFrom-failure-1-spec.k \
                   transferFrom-failure-2-spec.k

proof_dir:=tests/proofs
proof_tests:=$(proof_dir)/sum-to-n-spec.k \
			 $(patsubst %, $(proof_dir)/erc20/viper/%, $(erc20_files)) \
			 $(patsubst %, $(proof_dir)/erc20/zeppelin/%, $(erc20_files)) \
			 $(patsubst %, $(proof_dir)/erc20/hkg/%, $(erc20_files)) \
			 $(patsubst %, $(proof_dir)/erc20/hobby/%, $(hobby_erc20_files))

proof-test-all: proof-test
proof-test: $(proof_tests:=.test)

tests/proofs/%.test: tests/proofs/% build
	$(TEST) $<

split-proof-tests: $(proof_tests)

# #### Sum to N
tests/proofs/sum-to-n-spec.k: proofs/sum-to-n.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to "$(tangler)" --metadata="code:.sum-to-n" $< > $@

# #### ERC20
tests/proofs/erc20/viper/%-spec.k: proofs/erc20/tmpl.k proofs/erc20/viper/spec-viper.ini proofs/erc20/viper/pgm-viper.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 tests/gen-spec.py $^ $* > $@

tests/proofs/erc20/zeppelin/%-spec.k: proofs/erc20/tmpl.k proofs/erc20/zeppelin/spec-zeppelin.ini proofs/erc20/zeppelin/pgm-zeppelin.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 tests/gen-spec.py $^ $* > $@

tests/proofs/erc20/hkg/%-spec.k: proofs/erc20/tmpl.k proofs/erc20/hkg/spec-hkg.ini proofs/erc20/hkg/pgm-hkg.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 tests/gen-spec.py $^ $* > $@

tests/proofs/erc20/hobby/%-spec.k: proofs/erc20/tmpl.k proofs/erc20/hobby/spec-hobby.ini proofs/erc20/hobby/pgm-hobby.ini
	@echo >&2 "==  gen-spec: $@"
	mkdir -p $(dir $@)
	python3 tests/gen-spec.py $^ $* > $@

# InteractiveTests

interactive-test-all: interactive-test
interactive-test: \
	tests/interactive/gas-analysis/sumTo10.evm.test \
	tests/interactive/add0.json.test \
	tests/interactive/log3_MaxTopic_d0g0v0.json.test

tests/interactive/%.test: tests/interactive/% tests/interactive/%.out build
	$(TEST) $<

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
