# Common to all versions of K
# ===========================

.PHONY: all clean build defn vm-tests split-tests split-bchain-tests split-proof-tests test sphinx

all: build split-tests

clean:
	rm -r .build
	find tests/proofs/ -name '*.k' -delete

check_K_VERSION = $(if $(value K_VERSION),, $(error K_VERSION undefined, must be set))

K_VERSION_set:
	@:$(call check_K_VERSION)

build: K_VERSION_set defn .build/$(K_VERSION)/driver-kompiled/extras/timestamp
	@:$(call check_K_VERSION)

# Tangle definition from *.md files
# ---------------------------------

defn_dir=.build/$(K_VERSION)
defn_files=$(defn_dir)/driver.k $(defn_dir)/data.k $(defn_dir)/evm.k $(defn_dir)/analysis.k $(defn_dir)/krypto.k $(defn_dir)/verification.k
defn: K_VERSION_set $(defn_files)

.build/$(K_VERSION)/%.k: %.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to tangle.lua --metadata=code:"$(K_VERSION)" $< > $@

# Tests
# -----

split-tests: vm-tests split-bchain-tests split-proof-tests

tests/ethereum-tests/make.timestamp:
	@echo "==  git submodule: cloning upstreams test repository"
	git submodule update --init -- tests/ethereum-tests
	touch $@

tests/%/make.timestamp: tests/ethereum-tests/%.json
	@echo "==   split: $@"
	mkdir -p $(dir $@)
	tests/split-test.py $< $(dir $@)
	touch $@

blockchain_tests=$(wildcard tests/BlockchainTests/*/*/*/*.json)
vm_tests=$(wildcard tests/VMTests/*/*/*.json)
all_tests=$(vm_tests) $(blockchain_tests)
skipped_tests=$(wildcard tests/VMTests/vmPerformance/*/*.json) \
   $(wildcard tests/BlockchainTests/GeneralStateTests/*/*/*_Constantinople.json) \
   $(wildcard tests/BlockchainTests/GeneralStateTests/stQuadraticComplexityTest/*/*.json) \
   $(wildcard tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call50000*/*.json) \
   $(wildcard tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Return50000*/*.json) \
   $(wildcard tests/BlockchainTests/GeneralStateTests/stStaticCall/static_Call1MB1024Calldepth_d1g0v0/*.json)

passing_tests=$(filter-out $(skipped_tests), $(all_tests))
passing_vm_tests=$(filter-out $(skipped_tests), $(vm_tests))
passing_blockchain_tests=$(filter-out $(skipped_tests), $(blockchain_tests))
passing_targets=$(passing_tests:=.test)
passing_vm_targets=$(passing_vm_tests:=.test)
passing_blockchain_targets=$(passing_blockchain_tests:=.test)

test: $(passing_targets)
vm-test: $(passing_vm_targets)
blockchain-test: $(passing_blockchain_targets)

# ### VMTests

vm-tests: tests/ethereum-tests/make.timestamp

tests/VMTests/%.test: tests/VMTests/% build
	./vmtest $<

# ### BlockchainTests

split-bchain-tests: \
				  $(patsubst tests/ethereum-tests/%.json,tests/%/make.timestamp, $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/*/*.json))

tests/BlockchainTests/%.test: tests/BlockchainTests/% build
	./blockchaintest $<

# ### Proof Tests

proof_dir=tests/proofs
proof_files=$(proof_dir)/sum-to-n-spec.k \
			$(proof_dir)/hkg/allowance-spec.k \
			$(proof_dir)/hkg/approve-spec.k \
			$(proof_dir)/hkg/balanceOf-spec.k \
			$(proof_dir)/hkg/transfer-else-spec.k $(proof_dir)/hkg/transfer-then-spec.k \
			$(proof_dir)/hkg/transferFrom-else-spec.k $(proof_dir)/hkg/transferFrom-then-spec.k \
			$(proof_dir)/bad/hkg-token-buggy-spec.k

split-proof-tests: $(proof_files)

tests/proofs/sum-to-n-spec.k: proofs/sum-to-n.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to tangle.lua --metadata=code:sum-to-n $< > $@

tests/proofs/hkg/%-spec.k: proofs/hkg.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to tangle.lua --metadata=code:$* $< > $@

tests/proofs/bad/hkg-token-buggy-spec.k: proofs/token-buggy-spec.md
	@echo "==  tangle: $@"
	mkdir -p $(dir $@)
	pandoc --from markdown --to tangle.lua --metadata=code:k $< > $@

# UIUC K Specific
# ---------------

.build/uiuck/driver-kompiled/extras/timestamp: $(defn_files)
	@echo "== kompile: $@"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/uiuck

# RVK Specific
# ------------

.build/rvk/driver-kompiled/extras/timestamp: .build/rvk/driver-kompiled/interpreter
.build/rvk/driver-kompiled/interpreter: $(defn_files) KRYPTO.ml
	@echo "== kompile: $@"
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/rvk \
					--hook-namespaces KRYPTO --gen-ml-only -O3 --non-strict
	ocamlfind opt -c .build/rvk/driver-kompiled/constants.ml -package gmp -package zarith
	ocamlfind opt -c -I .build/rvk/driver-kompiled KRYPTO.ml -package cryptokit -package secp256k1 -package bn128
	ocamlfind opt -a -o semantics.cmxa KRYPTO.cmx
	ocamlfind remove ethereum-semantics-plugin
	ocamlfind install ethereum-semantics-plugin META semantics.cmxa semantics.a KRYPTO.cmi KRYPTO.cmx
	kompile --debug --main-module ETHEREUM-SIMULATION \
					--syntax-module ETHEREUM-SIMULATION $< --directory .build/rvk \
					--hook-namespaces KRYPTO --packages ethereum-semantics-plugin -O3 --non-strict
	cd .build/rvk/driver-kompiled && ocamlfind opt -o interpreter constants.cmx prelude.cmx plugin.cmx parser.cmx lexer.cmx run.cmx interpreter.ml -package gmp -package dynlink -package zarith -package str -package uuidm -package unix -package ethereum-semantics-plugin -linkpkg -inline 20 -nodynlink -O3 -linkall

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
	mkdir $(SPHINXBUILDDIR); \
	cp -r *.md proofs $(SPHINXBUILDDIR)/.; \
	cd $(SPHINXBUILDDIR); \
	pandoc --from markdown --to rst README.md --output index.rst; \
	sed -i 's/{.k[ a-zA-Z.-]*}/k/g' *.md proofs/*.md; \
	$(SPHINXBUILD) -b dirhtml $(ALLSPHINXOPTS) html; \
	$(SPHINXBUILD) -b text $(ALLSPHINXOPTS) html/text; \
	echo "[+] HTML generated in $(SPHINXBUILDDIR)/html, text in $(SPHINXBUILDDIR)/html/text"
