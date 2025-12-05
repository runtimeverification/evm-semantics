default: kevm-pyk


# Building
# --------

ifeq ($(shell command -v k-which-python),)
    PYTHON_BIN := python3.10
else
    PYTHON_BIN := $(shell k-which-python)
endif

KEVM_PYK_DIR := ./kevm-pyk
UV           := uv --project $(KEVM_PYK_DIR)
UV_RUN       := $(UV) run --

.PHONY: kevm-pyk
kevm-pyk:
	$(MAKE) -C $(KEVM_PYK_DIR)


# Tests
# -----

test: test-integration test-conformance test-prove test-interactive


# Conformance Tests

.PHONY: test-conformance
test-conformance:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_conformance.py"

.PHONY: conformance-failing-list
conformance-failing-list:
	cat /dev/null > tests/failing.llvm
	- $(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_conformance.py --save-failing --maxfail=10000"
	LC_ALL=en_US.UTF-8 sort -f -d -o tests/failing.llvm tests/failing.llvm
	if [ "$(shell uname)" = "Darwin" ]; then \
		sed -i '' '1{/^[[:space:]]*$$/d;}' tests/failing.llvm ;\
		echo >> tests/failing.llvm ;\
	else \
		sed -i '1{/^[[:space:]]*$$/d;}' tests/failing.llvm ;\
	fi

.PHONY: download-json-fixtures
download-json-fixtures:
	rm -rf tests/execution-spec-tests/fixtures
	cd tests/execution-spec-tests && bash get_execution_spec_tests.sh

test-fixtures: download-json-fixtures
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k 'test_execution_spec_tests.py and test_bchain'"

fixtures-failing-list: download-json-fixtures
	cat /dev/null > tests/execution-spec-tests/failing.llvm
	- $(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k 'test_execution_spec_tests.py and test_bchain' --save-failing --maxfail=10000 --numprocesses=28"
	LC_ALL=en_US.UTF-8 sort -f -d -o tests/execution-spec-tests/failing.llvm tests/execution-spec-tests/failing.llvm
	if [ "$(shell uname)" = "Darwin" ]; then \
		sed -i '' '1{/^[[:space:]]*$$/d;}' tests/execution-spec-tests/failing.llvm ;\
		echo >> tests/execution-spec-tests/failing.llvm ;\
	else \
		sed -i '1{/^[[:space:]]*$$/d;}' tests/execution-spec-tests/failing.llvm ;\
	fi

.PHONY: test-vm
test-vm:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_vm"

.PHONY: test-rest-vm
test-rest-vm:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_rest_vm"

.PHONY: test-bchain
test-bchain:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_bchain"

.PHONY: test-rest-bchain
test-rest-bchain:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_rest_bchain"


# Proof Tests

test-prove: test-prove-rules test-prove-functional test-prove-optimizations test-prove-dss

.PHONY: test-prove-rules
test-prove-rules:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_prove_rules"

.PHONY: test-prove-functional
test-prove-functional:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_prove_functional"

.PHONY: test-prove-optimizations
test-prove-optimizations:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_prove_optimizations"

.PHONY: test-prove-summaries
test-prove-summaries:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_prove_summaries"

.PHONY: test-prove-dss
test-prove-dss:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+="-k test_prove_dss"


# Integration Tests

.PHONY: test-integration
test-integration:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+='-k "(test_kast.py or test_run.py)"'

.PHONY: profile
profile:
	$(MAKE) -C kevm-pyk/ profile
	find /tmp/pytest-of-$$(whoami)/pytest-current/ -type f -name '*.prof' | sort | xargs tail -n +1

.PHONY: test-summarize
test-summarize:
	$(MAKE) -C kevm-pyk/ test-integration PYTEST_ARGS+='-k "test_summarize"'


# Smoke Tests

TEST_SYMBOLIC_BACKEND := haskell

KPROVE_MODULE = VERIFICATION
KPROVE_FILE   = verification
KPROVE_EXT    = k

KEVM_OPTS    ?=
KPROVE_OPTS  ?=

.SECONDEXPANSION:
tests/specs/%.prove: tests/specs/% tests/specs/$$(firstword $$(subst /, ,$$*))/$$(KPROVE_FILE)/$(TEST_SYMBOLIC_BACKEND)/timestamp
	$(UV_RUN) kevm-pyk prove $< $(KEVM_OPTS) $(KPROVE_OPTS) \
		--definition tests/specs/$(firstword $(subst /, ,$*))/$(KPROVE_FILE)/$(TEST_SYMBOLIC_BACKEND)

tests/specs/%/timestamp: tests/specs/$$(firstword $$(subst /, ,$$*))/$$(KPROVE_FILE).$$(KPROVE_EXT)
	$(UV_RUN) kevm-pyk kompile-spec                                                                             \
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
KEVM_SCHEDULE := CANCUN
KEVM_CHAINID  := 1

KRUN_OPTS     ?=

KEEP_OUTPUTS  := false
CHECK         := git --no-pager diff --no-index --ignore-all-space -R

tests/ethereum-tests/BlockchainTests/GeneralStateTests/VMTests/%: KEVM_MODE     = VMTESTS
tests/ethereum-tests/BlockchainTests/GeneralStateTests/VMTests/%: KEVM_SCHEDULE = DEFAULT

tests/%.run-interactive: tests/%
	$(UV_RUN) kevm-pyk run $< $(KEVM_OPTS) $(KRUN_OPTS) --target $(TEST_CONCRETE_BACKEND) \
	    --mode $(KEVM_MODE) --schedule $(KEVM_SCHEDULE) --chainid $(KEVM_CHAINID)         \
	    > tests/$*.$(TEST_CONCRETE_BACKEND)-out                                           \
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
