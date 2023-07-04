# Settings
# --------

UNAME_S := $(shell uname -s)

DEPS_DIR      := deps
BUILD_DIR     := .build
NODE_DIR      := $(abspath node)
BUILD_LOCAL   := $(abspath $(BUILD_DIR)/local)
LOCAL_LIB     := $(BUILD_LOCAL)/lib
LOCAL_BIN     := $(BUILD_LOCAL)/bin
export NODE_DIR
export LOCAL_LIB

INSTALL_PREFIX  := /usr
INSTALL_BIN     ?= $(INSTALL_PREFIX)/bin
INSTALL_LIB     ?= $(INSTALL_PREFIX)/lib/kevm
INSTALL_INCLUDE ?= $(INSTALL_LIB)/include

KEVM_BIN     := $(BUILD_DIR)$(INSTALL_BIN)
KEVM_LIB     := $(BUILD_DIR)$(INSTALL_LIB)
KEVM_INCLUDE := $(KEVM_LIB)/include
KEVM_K_BIN   := $(KEVM_LIB)/kframework/bin
KEVM         := kevm
KEVM_LIB_ABS := $(abspath $(KEVM_LIB))
export KEVM_LIB_ABS

KEVM_VERSION     ?= $(shell cat package/version)
KEVM_RELEASE_TAG ?= v$(KEVM_VERSION)-$(shell git rev-parse --short HEAD)

K_SUBMODULE := $(DEPS_DIR)/k

C_INCLUDE_PATH     += :$(BUILD_LOCAL)/include
CPLUS_INCLUDE_PATH += :$(BUILD_LOCAL)/include
PATH               := $(abspath $(KEVM_BIN)):$(abspath $(KEVM_K_BIN)):$(LOCAL_BIN):$(PATH)

export C_INCLUDE_PATH
export CPLUS_INCLUDE_PATH
export PATH

PLUGIN_SUBMODULE := $(DEPS_DIR)/plugin
PLUGIN_SOURCE    := $(KEVM_INCLUDE)/kframework/blockchain-k-plugin/krypto.md
PLUGIN_FULL_PATH := $(abspath ${PLUGIN_SUBMODULE})
export PLUGIN_FULL_PATH


.PHONY: all clean distclean                                                                                        \
        deps k-deps plugin-deps protobuf                                                                           \
        poetry-env poetry shell kevm-pyk                                                                           \
        build build-haskell build-haskell-standalone build-foundry build-llvm build-node build-kevm                \
        test                                                                                                       \
        test-integration test-conformance test-prove test-foundry-prove                                            \
        test-vm test-rest-vm test-bchain test-rest-bchain                                                          \
        test-node                                                                                                  \
        test-prove-smoke test-klab-prove                                                                           \
        test-interactive test-interactive-help test-interactive-run test-interactive-prove test-interactive-search \
        media media-pdf metropolis-theme                                                                           \
        install uninstall

.SECONDARY:

all: build

clean:
	rm -rf $(KEVM_BIN) $(KEVM_LIB)

distclean:
	rm -rf $(BUILD_DIR)

# Non-K Dependencies
# ------------------

protobuf_out     := $(LOCAL_LIB)/proto/proto/msg.pb.cc
protobuf:     $(protobuf_out)

$(protobuf_out): $(NODE_DIR)/proto/msg.proto
	@mkdir -p $(LOCAL_LIB)/proto
	protoc --cpp_out=$(LOCAL_LIB)/proto -I $(NODE_DIR) $(NODE_DIR)/proto/msg.proto


# K Dependencies
# --------------

deps: k-deps

K_MVN_ARGS :=
ifneq ($(SKIP_LLVM),)
    K_MVN_ARGS += -Dllvm.backend.skip
endif
ifneq ($(SKIP_HASKELL),)
    K_MVN_ARGS += -Dhaskell.backend.skip
endif

ifneq ($(APPLE_SILICON),)
    K_MVN_ARGS += -Dstack.extra-opts='--compiler ghc-8.10.7 --system-ghc'
endif

ifneq ($(RELEASE),)
    K_BUILD_TYPE := FastBuild
else
    K_BUILD_TYPE := Debug
endif

k-deps:
	cd $(K_SUBMODULE)                                                                                                                                                                            \
	    && mvn --batch-mode package -DskipTests -Dllvm.backend.prefix=$(INSTALL_LIB)/kframework -Dllvm.backend.destdir=$(CURDIR)/$(BUILD_DIR) -Dproject.build.type=$(K_BUILD_TYPE) $(K_MVN_ARGS) \
	    && DESTDIR=$(CURDIR)/$(BUILD_DIR) PREFIX=$(INSTALL_LIB)/kframework package/package

plugin_k_include  := $(KEVM_INCLUDE)/kframework/plugin
plugin_include    := $(KEVM_LIB)/blockchain-k-plugin/include
plugin_k          := krypto.md
plugin_c          := plugin_util.cpp crypto.cpp blake2.cpp plugin_util.h blake2.h
plugin_needed_lib := libcryptopp libff libsecp256k1
plugin_includes   := $(patsubst %, $(plugin_k_include)/%, $(plugin_k))
plugin_c_includes := $(patsubst %, $(plugin_include)/c/%, $(plugin_c))
plugin_needed_libs := $(patsubst %, $(KEVM_LIB)/%, $(plugin_needed_lib))

$(plugin_include)/c/%: $(PLUGIN_SUBMODULE)/plugin-c/%
	@mkdir -p $(dir $@)
	install $< $@

$(plugin_k_include)/%: $(PLUGIN_SUBMODULE)/plugin/%
	@mkdir -p $(dir $@)
	install $< $@


$(KEVM_LIB)/%: $(PLUGIN_SUBMODULE)/build/%
	@mkdir -p $(dir $@)
	cp -r $< $@

$(PLUGIN_SUBMODULE)/build/lib%:
	cd $(PLUGIN_SUBMODULE) && make lib$*

plugin-deps: $(plugin_includes) $(plugin_c_includes) $(plugin_needed_libs)


# Building
# --------

PYTHON_BIN   := python3.10
KEVM_PYK_DIR := ./kevm-pyk
POETRY       := poetry -C $(KEVM_PYK_DIR)
POETRY_RUN   := $(POETRY) run --

poetry-env:
	$(POETRY) env use $(PYTHON_BIN)

poetry: poetry-env
	$(POETRY) install

shell: poetry
	$(POETRY) shell

kevm-pyk: poetry-env
	$(MAKE) -C $(KEVM_PYK_DIR)

kevm_files := abi.md                          \
              asm.md                          \
              buf.md                          \
              data.md                         \
              driver.md                       \
              edsl.md                         \
              evm.md                          \
              evm-types.md                    \
              evm-node.md                     \
              foundry.md                      \
              hashed-locations.md             \
              gas.md                          \
              json-rpc.md                     \
              network.md                      \
              optimizations.md                \
              schedule.md                     \
              serialization.md                \
              state-utils.md                  \
              word.md                         \
              lemmas/lemmas.k                 \
              lemmas/evm-int-simplification.k \
              lemmas/int-simplification.k     \
              lemmas/bitwise-simplification.k \
              lemmas/bytes-simplification.k

kevm_includes := $(patsubst %, $(KEVM_INCLUDE)/kframework/%, $(kevm_files))

includes := $(kevm_includes) $(plugin_includes) $(plugin_c_includes)

$(KEVM_INCLUDE)/%: include/%
	@mkdir -p $(dir $@)
	install $< $@

$(KEVM_INCLUDE)/kframework/lemmas/%.k: tests/specs/%.k
	@mkdir -p $(dir $@)
	install $< $@

KEVM_PYK              := $(POETRY_RUN) kevm-pyk
KOMPILE               := KEVM_LIB=$(KEVM_LIB) $(KEVM_PYK) kompile
KOMPILE_MAIN_FILE     :=
KOMPILE_TARGET        :=
KOMPILE_MAIN_MODULE   :=
KOMPILE_SYNTAX_MODULE :=

KOMPILE_OPTS :=
ifneq (,$(RELEASE))
    KOMPILE_OPTS += -O2
else
    KOMPILE_OPTS += -O1
endif

kompile =                                        \
    $(KOMPILE)                                   \
        $(KOMPILE_MAIN_FILE)                     \
        --target $(KOMPILE_TARGET)               \
        --main-module $(KOMPILE_MAIN_MODULE)     \
        --syntax-module $(KOMPILE_SYNTAX_MODULE) \
        $(KOMPILE_OPTS)


# Haskell

haskell_dir      := haskell
haskell_kompiled := $(haskell_dir)/definition.kore
kompile_haskell  := $(KEVM_LIB)/$(haskell_kompiled)

ifeq ($(UNAME_S),Darwin)
$(kompile_haskell): $(libsecp256k1_out)
endif

$(kompile_haskell): $(kevm_includes) $(plugin_includes)

$(kompile_haskell): KOMPILE_TARGET        := haskell
$(kompile_haskell): KOMPILE_MAIN_FILE     := $(KEVM_INCLUDE)/kframework/edsl.md
$(kompile_haskell): KOMPILE_MAIN_MODULE   := EDSL
$(kompile_haskell): KOMPILE_SYNTAX_MODULE := EDSL
$(kompile_haskell):
	$(kompile)


# Standalone

llvm_dir      := llvm
llvm_kompiled := $(llvm_dir)/interpreter
kompile_llvm  := $(KEVM_LIB)/$(llvm_kompiled)



$(kompile_llvm): $(kevm_includes) $(plugin_includes) $(plugin_c_includes)

$(kompile_llvm): KOMPILE_TARGET        := llvm
$(kompile_llvm): KOMPILE_MAIN_FILE     := $(KEVM_INCLUDE)/kframework/driver.md
$(kompile_llvm): KOMPILE_MAIN_MODULE   := ETHEREUM-SIMULATION
$(kompile_llvm): KOMPILE_SYNTAX_MODULE := ETHEREUM-SIMULATION
$(kompile_llvm):
	$(kompile)


# Haskell Standalone

haskell_standalone_dir      := haskell-standalone
haskell_standalone_kompiled := $(haskell_standalone_dir)/definition.kore
kompile_haskell_standalone  := $(KEVM_LIB)/$(haskell_standalone_kompiled)


$(kompile_haskell_standalone): $(kevm_includes) $(plugin_includes)

$(kompile_haskell_standalone): KOMPILE_TARGET        := haskell-standalone
$(kompile_haskell_standalone): KOMPILE_MAIN_FILE     := $(KEVM_INCLUDE)/kframework/driver.md
$(kompile_haskell_standalone): KOMPILE_MAIN_MODULE   := ETHEREUM-SIMULATION
$(kompile_haskell_standalone): KOMPILE_SYNTAX_MODULE := ETHEREUM-SIMULATION
$(kompile_haskell_standalone):
	$(kompile)


# Node
#
node_dir      := node
node_kore     := $(node_dir)/definition.kore
node_kompiled := $(node_dir)/build/kevm-vm
kompile_node  := $(KEVM_LIB)/$(node_kore)
export node_dir

$(kompile_node): $(kevm_includes) $(plugin_includes) $(plugin_c_includes)

$(kompile_node): KOMPILE_TARGET        := node
$(kompile_node): KOMPILE_MAIN_FILE     := $(KEVM_INCLUDE)/kframework/evm-node.md
$(kompile_node): KOMPILE_MAIN_MODULE   := EVM-NODE
$(kompile_node): KOMPILE_SYNTAX_MODULE := EVM-NODE
$(kompile_node):
	$(kompile)


$(KEVM_LIB)/$(node_kompiled): $(KEVM_LIB)/$(node_kore) $(protobuf_out)
	@mkdir -p $(dir $@)
	cd $(dir $@) && cmake $(CURDIR)/cmake/node -DCMAKE_INSTALL_PREFIX=$(INSTALL_LIB)/$(node_dir) -DCMAKE_CXX_FLAGS=-std=c++17 && $(MAKE)


# Foundry

foundry_dir      := foundry
foundry_kompiled := $(foundry_dir)/definition.kore
kompile_foundry  := $(KEVM_LIB)/$(foundry_kompiled)


$(kompile_foundry): $(kevm_includes) $(plugin_includes) $(lemma_includes)

$(kompile_foundry): KOMPILE_TARGET        := foundry
$(kompile_foundry): KOMPILE_MAIN_FILE     := $(KEVM_INCLUDE)/kframework/foundry.md
$(kompile_foundry): KOMPILE_MAIN_MODULE   := FOUNDRY
$(kompile_foundry): KOMPILE_SYNTAX_MODULE := FOUNDRY
$(kompile_foundry):
	$(kompile)


# Installing
# ----------

install_bins := kevm    \
                kevm-vm

install_libs := $(haskell_kompiled)                                        \
                $(llvm_kompiled)                                           \
                $(foundry_kompiled)                                        \
                $(haskell_standalone_kompiled)                             \
                $(patsubst %, include/kframework/lemmas/%, $(kevm_lemmas)) \
                kore-json.py                                               \
                release.md                                                 \
                version

$(KEVM_BIN)/%: bin/%
	@mkdir -p $(dir $@)
	install $< $@

$(KEVM_BIN)/kevm-vm: $(KEVM_LIB)/$(node_kompiled)
	@mkdir -p $(dir $@)
	install $< $@

$(KEVM_LIB)/%.py: scripts/%.py
	@mkdir -p $(dir $@)
	install $< $@

$(KEVM_LIB)/version: package/version
	@mkdir -p $(dir $@)
	install $< $@

$(KEVM_LIB)/release.md: INSTALL.md
	@mkdir -p $(dir $@)
	echo "KEVM Release $(shell cat package/version)"  > $@
	echo                                             >> $@
	cat INSTALL.md                                   >> $@

build: $(patsubst %, $(KEVM_BIN)/%, $(install_bins)) $(patsubst %, $(KEVM_LIB)/%, $(install_libs))

build-llvm:               $(KEVM_LIB)/$(llvm_kompiled)    $(KEVM_LIB)/kore-json.py
build-haskell:            $(KEVM_LIB)/$(haskell_kompiled) $(KEVM_LIB)/kore-json.py
build-haskell-standalone: $(KEVM_LIB)/$(haskell_standalone_kompiled) $(KEVM_LIB)/kore-json.py
build-node:               $(KEVM_LIB)/$(node_kompiled)
build-kevm:               $(KEVM_BIN)/kevm $(KEVM_LIB)/version $(kevm_includes) $(plugin_includes)
build-foundry:            $(KEVM_BIN)/kevm $(KEVM_LIB)/$(foundry_kompiled) $(KEVM_LIB)/kore-json.py

all_bin_sources := $(shell find $(KEVM_BIN) -type f | sed 's|^$(KEVM_BIN)/||')
all_lib_sources := $(shell find $(KEVM_LIB) -type f                                            \
                            -not -path "$(KEVM_LIB)/**/dt/*"                                   \
                            -not -path "$(KEVM_LIB)/kframework/share/kframework/pl-tutorial/*" \
                            -not -path "$(KEVM_LIB)/kframework/share/kframework/k-tutorial/*"  \
                        | sed 's|^$(KEVM_LIB)/||')

install: $(patsubst %, $(DESTDIR)$(INSTALL_BIN)/%, $(all_bin_sources)) \
         $(patsubst %, $(DESTDIR)$(INSTALL_LIB)/%, $(all_lib_sources))

$(DESTDIR)$(INSTALL_BIN)/%: $(KEVM_BIN)/%
	@mkdir -p $(dir $@)
	install $< $@

$(DESTDIR)$(INSTALL_LIB)/%: $(KEVM_LIB)/%
	@mkdir -p $(dir $@)
	install $< $@

uninstall:
	rm -rf $(DESTDIR)$(INSTALL_BIN)/kevm
	rm -rf $(DESTDIR)$(INSTALL_LIB)/kevm

# Tests
# -----

TEST_CONCRETE_BACKEND := llvm
TEST_SYMBOLIC_BACKEND := haskell

CHECK := git --no-pager diff --no-index --ignore-all-space -R

KEVM_MODE     := NORMAL
KEVM_SCHEDULE := MERGE
KEVM_CHAINID  := 1

KPROVE_MODULE  = VERIFICATION
KPROVE_FILE    = verification
KPROVE_EXT     = k

KEVM_OPTS    ?=
KPROVE_OPTS  ?=
KAST_OPTS    ?=
KRUN_OPTS    ?=
KSEARCH_OPTS ?=

KEEP_OUTPUTS := false

test: test-integration test-conformance test-prove test-interactive

# Generic Test Harnesses

tests/ethereum-tests/LegacyTests/Constantinople/VMTests/%: KEVM_MODE     = VMTESTS
tests/ethereum-tests/LegacyTests/Constantinople/VMTests/%: KEVM_SCHEDULE = DEFAULT

tests/%.run: tests/%
	$(KEVM) interpret $< $(KEVM_OPTS) $(KRUN_OPTS) --backend $(TEST_CONCRETE_BACKEND)                                  \
	    --mode $(KEVM_MODE) --schedule $(KEVM_SCHEDULE) --chainid $(KEVM_CHAINID)                                      \
	    > tests/$*.$(TEST_CONCRETE_BACKEND)-out                                                                        \
	    || $(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out tests/templates/output-success-$(TEST_CONCRETE_BACKEND).json
	$(KEEP_OUTPUTS) || rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.run-interactive: tests/%
	$(KEVM) run $< $(KEVM_OPTS) $(KRUN_OPTS) --backend $(TEST_CONCRETE_BACKEND)                                        \
	    --mode $(KEVM_MODE) --schedule $(KEVM_SCHEDULE) --chainid $(KEVM_CHAINID)                                      \
	    > tests/$*.$(TEST_CONCRETE_BACKEND)-out                                                                        \
	    || $(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out tests/templates/output-success-$(TEST_CONCRETE_BACKEND).json
	$(KEEP_OUTPUTS) || rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.run-expected: tests/% tests/%.expected
	$(KEVM) run $< $(KEVM_OPTS) $(KRUN_OPTS) --backend $(TEST_CONCRETE_BACKEND)    \
	    --mode $(KEVM_MODE) --schedule $(KEVM_SCHEDULE) --chainid $(KEVM_CHAINID)  \
	    > tests/$*.$(TEST_CONCRETE_BACKEND)-out                                    \
	    || $(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out tests/$*.expected
	$(KEEP_OUTPUTS) || rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/interactive/%.json.gst-to-kore.check: tests/ethereum-tests/GeneralStateTests/VMTests/%.json $(KEVM_BIN)/kevm
	$(KEVM) kast $< $(KEVM_OPTS) $(KAST_OPTS) > tests/interactive/$*.gst-to-kore.out
	$(CHECK) tests/interactive/$*.gst-to-kore.out tests/interactive/$*.gst-to-kore.expected
	$(KEEP_OUTPUTS) || rm -rf tests/interactive/$*.gst-to-kore.out

# solc-to-k
# ---------

PYTEST_PARALLEL := 8
PYTEST_ARGS     :=

test-foundry-prove: poetry build-kevm build-foundry
	$(MAKE) -C kevm-pyk/ test-integration TEST_ARGS+="-k test_foundry_prove.py -n$(PYTEST_PARALLEL) $(PYTEST_ARGS)"

tests/specs/examples/%-bin-runtime.k: KEVM_OPTS += --pyk --verbose
tests/specs/examples/%-bin-runtime.k: KEVM := $(POETRY_RUN) kevm

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
	$(POETRY_RUN) $(KEVM) prove $< $(KEVM_OPTS) --backend $(TEST_SYMBOLIC_BACKEND) $(KPROVE_OPTS) \
	    --definition tests/specs/$(firstword $(subst /, ,$*))/$(KPROVE_FILE)/$(TEST_SYMBOLIC_BACKEND)

tests/specs/%/timestamp: tests/specs/$$(firstword $$(subst /, ,$$*))/$$(KPROVE_FILE).$$(KPROVE_EXT) $(kevm_includes) $(plugin_includes)
	$(KOMPILE)                                                                                                  \
		$<                                                                                                      \
		--target $(word 3, $(subst /, , $*))                                                                    \
	    --output-definition tests/specs/$(firstword $(subst /, ,$*))/$(KPROVE_FILE)/$(word 3, $(subst /, , $*)) \
	    --main-module $(KPROVE_MODULE)                                                                          \
	    --syntax-module $(KPROVE_MODULE)                                                                        \
	    $(KOMPILE_OPTS)

tests/%.search: tests/%
	$(KEVM) search $< "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" $(KEVM_OPTS) $(KSEARCH_OPTS) --backend $(TEST_SYMBOLIC_BACKEND) > $@-out
	$(CHECK) $@-out $@-expected
	$(KEEP_OUTPUTS) || rm -rf $@-out

# Smoke Tests

smoke_tests_run = tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmArithmeticTest/add0.json      \
                  tests/ethereum-tests/LegacyTests/Constantinople/VMTests/vmIOandFlowOperations/pop1.json \
                  tests/interactive/sumTo10.evm

smoke_tests_prove=tests/specs/erc20/ds/transfer-failure-1-a-spec.k

# Conformance Tests

test-conformance: poetry build-kevm build-llvm
	$(MAKE) -C kevm-pyk/ test-integration TEST_ARGS+="-k test_conformance.py -n$(PYTEST_PARALLEL) $(PYTEST_ARGS)"

test-vm: poetry build-kevm build-llvm
	$(MAKE) -C kevm-pyk/ test-integration TEST_ARGS+="-k test_vm -n$(PYTEST_PARALLEL) $(PYTEST_ARGS)"

test-rest-vm: poetry build-kevm build-llvm
	$(MAKE) -C kevm-pyk/ test-integration TEST_ARGS+="-k test_rest_vm -n$(PYTEST_PARALLEL) $(PYTEST_ARGS)"

test-bchain: poetry build-kevm build-llvm
	$(MAKE) -C kevm-pyk/ test-integration TEST_ARGS+="-k test_bchain -n$(PYTEST_PARALLEL) $(PYTEST_ARGS)"

test-rest-bchain: poetry build-kevm build-llvm
	$(MAKE) -C kevm-pyk/ test-integration TEST_ARGS+="-k test_rest_bchain -n$(PYTEST_PARALLEL) $(PYTEST_ARGS)"

# Proof Tests

prove_smoke_tests := $(shell cat tests/specs/smoke)

test-prove: tests/specs/opcodes/evm-optimizations-spec.md poetry build-kevm build-haskell
	$(MAKE) -C kevm-pyk/ test-integration TEST_ARGS+="-k test_prove -n$(PYTEST_PARALLEL) $(PYTEST_ARGS)"

test-prove-smoke: $(prove_smoke_tests:=.prove)

test-klab-prove: KPROVE_OPTS += --debugger
test-klab-prove: $(smoke_tests_prove:=.prove)

# to generate optimizations.md, run: ./optimizer/optimize.sh &> output
tests/specs/opcodes/evm-optimizations-spec.md: include/kframework/optimizations.md
	cat $< | sed 's/^rule/claim/' | sed 's/EVM-OPTIMIZATIONS/EVM-OPTIMIZATIONS-SPEC/' | grep -v 'priority(40)' > $@

# Integration Tests

test-integration: poetry build-kevm build-haskell build-llvm
	$(MAKE) -C kevm-pyk/ test-integration TEST_ARGS+='-k "(test_kast.py or test_run.py or test_solc_to_k.py)" -n$(PYTEST_PARALLEL) $(PYTEST_ARGS)'

# Interactive Tests

test-interactive: test-interactive-run test-interactive-prove test-interactive-search test-interactive-help

test-interactive-run: $(smoke_tests_run:=.run-interactive)
test-interactive-prove: $(smoke_tests_prove:=.prove)

search_tests:=$(wildcard tests/interactive/search/*.evm)
test-interactive-search: $(search_tests:=.search)

test-interactive-help:
	$(KEVM) help

proto_tester := $(LOCAL_BIN)/proto_tester
proto-tester: $(proto_tester)
$(proto_tester): tests/vm/proto_tester.cpp
	@mkdir -p $(LOCAL_BIN)
	$(CXX) -I $(LOCAL_LIB)/proto $(protobuf_out) $< -o $@ -lprotobuf -lpthread

node_tests:=$(wildcard tests/vm/*.bin)
test-node: $(node_tests:=.run-node)

tests/vm/%.run-node: tests/vm/%.expected $(KEVM_BIN)/kevm-vm $(proto_tester)
	bash -c " \
	  kevm-vm 8888 127.0.0.1 & \
	  while ! netcat -z 127.0.0.1 8888; do sleep 0.1; done; \
	  netcat -N 127.0.0.1 8888 < tests/vm/$* > tests/vm/$*.out; \
	  kill %kevm-vm || true"
	$(proto_tester) $< tests/vm/$*.out

# Media
# -----

media: media-pdf

### Media generated PDFs

media_pdfs := 201710-presentation-devcon3                          \
              201801-presentation-csf                              \
              201905-exercise-k-workshop                           \
              201908-trufflecon-workshop 201908-trufflecon-firefly

media/%.pdf: media/%.md media/citations.md
	@mkdir -p $(dir $@)
	cat $^ | pandoc --from markdown --filter pandoc-citeproc --to beamer --output $@

media-pdf: $(patsubst %, media/%.pdf, $(media_pdfs))

metropolis-theme: $(BUILD_DIR)/media/metropolis/beamerthememetropolis.sty

$(BUILD_DIR)/media/metropolis/beamerthememetropolis.sty:
	cd $(dir $@) && $(MAKE)
