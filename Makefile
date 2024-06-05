all: poetry


# Building
# --------

PYTHON_BIN   := python3.10
KEVM_PYK_DIR := ./kevm-pyk
POETRY       := poetry -C $(KEVM_PYK_DIR)
POETRY_RUN   := $(POETRY) run --


.PHONY: poetry-env
poetry-env:
	$(POETRY) env use $(PYTHON_BIN)

poetry: poetry-env
	$(POETRY) install

shell: poetry
	$(POETRY) shell

kevm-pyk: poetry-env
	$(MAKE) -C $(KEVM_PYK_DIR)


# Tests
# -----

test: test-integration test-conformance test-prove test-prove-pyk test-prove-kprove test-prove-dss test-interactive


# Conformance Tests

test-conformance: poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_conformance.py"

test-vm: poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_vm"

test-rest-vm: poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_rest_vm"

test-bchain: poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_bchain"

test-rest-bchain: poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_rest_bchain"


# Proof Tests

test-prove: test-prove-pyk test-prove-kprove test-prove-dss

test-prove-pyk: tests/specs/opcodes/evm-optimizations-spec.md poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_pyk_prove"

test-prove-kprove: tests/specs/opcodes/evm-optimizations-spec.md poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_kprove_prove"

test-prove-dss: poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_prove_dss"

# to generate optimizations.md, run: ./optimizer/optimize.sh &> output
tests/specs/opcodes/evm-optimizations-spec.md: kevm-pyk/src/kevm_pyk/kproj/evm-semantics/optimizations.md
	cat kevm-pyk/src/kevm_pyk/kproj/evm-semantics/optimizations.md | sed 's/^  rule/  claim/' | sed 's/EVM-OPTIMIZATIONS/EVM-OPTIMIZATIONS-SPEC/' | grep -v 'priority(40)' > $@


# Integration Tests

test-integration: poetry
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+='-k "(test_kast.py or test_run.py or test_solc_to_k.py)"'

profile: poetry
	$(MAKE) -C kevm-pyk/ profile
	find /tmp/pytest-of-$$(whoami)/pytest-current/ -type f -name '*.prof' | sort | xargs tail -n +1


# Smoke Tests

TEST_SYMBOLIC_BACKEND := haskell

KPROVE_MODULE = VERIFICATION
KPROVE_FILE   = verification
KPROVE_EXT    = k

KEVM_OPTS    ?=
KPROVE_OPTS  ?=


tests/specs/examples/%-bin-runtime.k: KEVM_OPTS += --verbose

tests/specs/examples/erc20-spec/haskell/timestamp: tests/specs/examples/erc20-bin-runtime.k
tests/specs/examples/erc20-bin-runtime.k: tests/specs/examples/ERC20.sol $(KEVM_LIB)/$(haskell_kompiled) poetry
	$(KEVM) solc-to-k $< ERC20 $(KEVM_OPTS) --verbose --definition $(KEVM_LIB)/$(haskell_dir) --main-module ERC20-VERIFICATION > $@

tests/specs/examples/erc721-spec/haskell/timestamp: tests/specs/examples/erc721-bin-runtime.k
tests/specs/examples/erc721-bin-runtime.k: tests/specs/examples/ERC721.sol $(KEVM_LIB)/$(haskell_kompiled) poetry
	$(KEVM) solc-to-k $< ERC721 $(KEVM_OPTS) --verbose --definition $(KEVM_LIB)/$(haskell_dir) --main-module ERC721-VERIFICATION > $@

tests/specs/examples/storage-spec/haskell/timestamp: tests/specs/examples/storage-bin-runtime.k
tests/specs/examples/storage-bin-runtime.k: tests/specs/examples/Storage.sol $(KEVM_LIB)/$(haskell_kompiled) poetry
	$(KEVM) solc-to-k $< Storage $(KEVM_OPTS) --verbose --definition $(KEVM_LIB)/$(haskell_dir) --main-module STORAGE-VERIFICATION > $@

tests/specs/examples/empty-bin-runtime.k: tests/specs/examples/Empty.sol $(KEVM_LIB)/$(haskell_kompiled) poetry
	$(KEVM) solc-to-k $< Empty $(KEVM_OPTS) --verbose --definition $(KEVM_LIB)/$(haskell_dir) --main-module EMPTY-VERIFICATION > $@

.SECONDEXPANSION:
tests/specs/%.prove: tests/specs/% tests/specs/$$(firstword $$(subst /, ,$$*))/$$(KPROVE_FILE)/$(TEST_SYMBOLIC_BACKEND)/timestamp
	$(POETRY_RUN) kevm-pyk prove $< $(KEVM_OPTS) $(KPROVE_OPTS) \
		--definition tests/specs/$(firstword $(subst /, ,$*))/$(KPROVE_FILE)/$(TEST_SYMBOLIC_BACKEND)

tests/specs/%/timestamp: tests/specs/$$(firstword $$(subst /, ,$$*))/$$(KPROVE_FILE).$$(KPROVE_EXT)
	$(POETRY_RUN) kevm-pyk kompile-spec                                                                         \
		$<                                                                                                      \
		--target $(word 3, $(subst /, , $*))                                                                    \
		--output-definition tests/specs/$(firstword $(subst /, ,$*))/$(KPROVE_FILE)/$(word 3, $(subst /, , $*)) \
		--main-module $(KPROVE_MODULE)                                                                          \
		--syntax-module $(KPROVE_MODULE)                                                                        \
		$(KOMPILE_OPTS)

prove_smoke_tests := $(shell cat tests/specs/smoke)

.PHONY: test-prove-smoke
test-prove-smoke: $(prove_smoke_tests:=.prove)


# Interactive Tests

TEST_CONCRETE_BACKEND := llvm

KEVM_MODE     := NORMAL
KEVM_SCHEDULE := SHANGHAI
KEVM_CHAINID  := 1

KRUN_OPTS     ?=

KEEP_OUTPUTS  := false
CHECK         := git --no-pager diff --no-index --ignore-all-space -R

tests/ethereum-tests/BlockchainTests/GeneralStateTests/VMTests/%: KEVM_MODE     = VMTESTS
tests/ethereum-tests/BlockchainTests/GeneralStateTests/VMTests/%: KEVM_SCHEDULE = DEFAULT

tests/%.run-interactive: tests/%
	$(POETRY_RUN) kevm-pyk run $< $(KEVM_OPTS) $(KRUN_OPTS) --target $(TEST_CONCRETE_BACKEND)                          \
	    --mode $(KEVM_MODE) --schedule $(KEVM_SCHEDULE) --chainid $(KEVM_CHAINID)                                      \
	    > tests/$*.$(TEST_CONCRETE_BACKEND)-out                                                                        \
	    || $(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out tests/templates/output-success-$(TEST_CONCRETE_BACKEND).json
	$(KEEP_OUTPUTS) || rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

interactive_tests = tests/interactive/add.json    \
                    tests/interactive/sumTo10.evm

.PHONY: test-interactive
test-interactive: $(interactive_tests:=.run-interactive)


# Media
# -----

media: media-pdf

### Media generated PDFs

.PHONY: media_pdfs
media_pdfs := 201710-presentation-devcon3                          \
              201801-presentation-csf                              \
              201905-exercise-k-workshop                           \
              201908-trufflecon-workshop 201908-trufflecon-firefly

media/%.pdf: media/%.md media/citations.md
	@mkdir -p $(dir $@)
	cat $^ | pandoc --from markdown --filter pandoc-citeproc --to beamer --output $@

.PHONY: media-pdf
media-pdf: $(patsubst %, media/%.pdf, $(media_pdfs))

.PHONY: metropolis-theme
metropolis-theme: $(BUILD_DIR)/media/metropolis/beamerthememetropolis.sty

$(BUILD_DIR)/media/metropolis/beamerthememetropolis.sty:
	cd $(dir $@) && $(MAKE)
