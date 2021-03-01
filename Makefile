# Settings
# --------

UNAME_S := $(shell uname -s)

DEPS_DIR      := deps
BUILD_DIR     := .build
SUBDEFN_DIR   := .
DEFN_BASE_DIR := $(BUILD_DIR)/defn
DEFN_DIR      := $(DEFN_BASE_DIR)/$(SUBDEFN_DIR)
BUILD_LOCAL   := $(abspath $(BUILD_DIR)/local)
LOCAL_LIB     := $(BUILD_LOCAL)/lib

KEVM_BIN     := $(BUILD_DIR)/bin
KEVM_LIB     := $(BUILD_DIR)/lib/kevm
KEVM_INCLUDE := $(KEVM_LIB)/include
KEVM_K_BIN   := $(KEVM_LIB)/kframework/bin
KEVM         := kevm

KEVM_VERSION     ?= 1.0.1
KEVM_RELEASE_TAG ?= v$(KEVM_VERSION)-$(shell git rev-parse --short HEAD)

INSTALL_PREFIX  := /usr
INSTALL_BIN     ?= $(DESTDIR)$(INSTALL_PREFIX)/bin
INSTALL_LIB     ?= $(DESTDIR)$(INSTALL_PREFIX)/lib/kevm
INSTALL_INCLUDE ?= $(INSTALL_LIB)/include

K_SUBMODULE := $(DEPS_DIR)/k
K_INSTALL   := $(DESTDIR)$(INSTALL_PREFIX)/kframework
K_JAR       := $(K_INSTALL)/lib/kframework/java/kernel-1.0-SNAPSHOT.jar

LIBRARY_PATH         := $(LOCAL_LIB)
C_INCLUDE_PATH       += :$(BUILD_LOCAL)/include
CPLUS_INCLUDE_PATH   += :$(BUILD_LOCAL)/include
PATH                 := $(KEVM_BIN):$(KEVM_K_BIN):$(PATH)

export LIBRARY_PATH
export C_INCLUDE_PATH
export CPLUS_INCLUDE_PATH
export PATH

PLUGIN_SUBMODULE := $(abspath $(DEPS_DIR)/plugin)
PLUGIN_SOURCE    := $(KEVM_INCLUDE)/kframework/blockchain-k-plugin/krypto.md
export PLUGIN_SUBMODULE

.PHONY: all clean distclean                                                                                                      \
        deps all-deps llvm-deps haskell-deps k-deps plugin-deps libsecp256k1 libff                                               \
        build build-java build-haskell build-llvm                                                                                \
        test test-all test-conformance test-rest-conformance test-all-conformance test-slow-conformance test-failing-conformance \
        test-vm test-rest-vm test-all-vm test-bchain test-rest-bchain test-all-bchain                                            \
        test-prove test-failing-prove                                                                                            \
        test-prove-benchmarks test-prove-functional test-prove-opcodes test-prove-erc20 test-prove-bihu test-prove-examples      \
        test-prove-mcd test-klab-prove test-haskell-dry-run                                                                      \
        test-parse test-failure                                                                                                  \
        test-interactive test-interactive-help test-interactive-run test-interactive-prove test-interactive-search               \
        media media-pdf metropolis-theme                                                                                         \
        install uninstall
.SECONDARY:

all: build

clean:
	rm -rf $(KEVM_BIN) $(KEVM_LIB)

distclean:
	rm -rf $(BUILD_DIR)
	git clean -dffx -- tests/

# Non-K Dependencies
# ------------------

libsecp256k1_out := $(LOCAL_LIB)/pkgconfig/libsecp256k1.pc
libff_out        := $(LOCAL_LIB)/libff.a

libsecp256k1: $(libsecp256k1_out)
libff:        $(libff_out)

$(libsecp256k1_out): $(PLUGIN_SUBMODULE)/deps/secp256k1/autogen.sh
	cd $(PLUGIN_SUBMODULE)/deps/secp256k1                                 \
	    && ./autogen.sh                                                   \
	    && ./configure --enable-module-recovery --prefix="$(BUILD_LOCAL)" \
	    && $(MAKE)                                                        \
	    && $(MAKE) install

ifeq ($(UNAME_S),Linux)
    LIBFF_CMAKE_FLAGS=
else
    LIBFF_CMAKE_FLAGS=-DWITH_PROCPS=OFF
endif

$(libff_out): $(PLUGIN_SUBMODULE)/deps/libff/CMakeLists.txt
	@mkdir -p $(PLUGIN_SUBMODULE)/deps/libff/build
	cd $(PLUGIN_SUBMODULE)/deps/libff/build                                                               \
	    && cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=$(BUILD_LOCAL) $(LIBFF_CMAKE_FLAGS) \
	    && make -s -j4                                                                                    \
	    && make install

# K Dependencies
# --------------

deps: k-deps plugin-deps

k-deps: $(K_JAR)

plugin-deps: $(PLUGIN_SOURCE)

$(PLUGIN_SOURCE): $(PLUGIN_SUBMODULE)/plugin/krypto.md
	cd deps/plugin && make INSTALL_PREFIX=$(CURDIR)/$(KEVM_LIB) install

K_MVN_ARGS :=
ifneq ($(SKIP_LLVM),)
    K_MVN_ARGS += -Dllvm.backend.skip
endif
ifneq ($(SKIP_HASKELL),)
    K_MVN_ARGS += -Dhaskell.backend.skip
endif

ifneq ($(RELEASE),)
    K_BUILD_TYPE := FastBuild
else
    K_BUILD_TYPE := Debug
endif

$(K_JAR):
	cd $(K_SUBMODULE)                                                                                                                                                             \
	    && mvn --batch-mode package -DskipTests -Dllvm.backend.prefix=/kframework -Dllvm.backend.destdir=$(CURDIR)/$(KEVM_LIB) -Dproject.build.type=$(K_BUILD_TYPE) $(K_MVN_ARGS) \
	    && DESTDIR=$(CURDIR)/$(KEVM_LIB) PREFIX=/kframework package/package

# Building
# --------

SOURCE_FILES       := abi                        \
                      asm                        \
                      buf                        \
                      data                       \
                      driver                     \
                      edsl                       \
                      evm                        \
                      evm-types                  \
                      hashed-locations           \
                      json-rpc                   \
                      network                    \
                      serialization              \
                      state-loader               \
                      blockchain-k-plugin/krypto
EXTRA_SOURCE_FILES :=
ALL_FILES          := $(patsubst %, %.md, $(SOURCE_FILES) $(EXTRA_SOURCE_FILES))

includes := $(patsubst %, $(KEVM_INCLUDE)/kframework/%, $(ALL_FILES))

$(KEVM_INCLUDE)/kframework/%.md: %.md
	install -D $< $@

tangle_concrete := k & (! ceil) & ( ( ! ( symbolic | nobytes ) ) | concrete | bytes   )
tangle_java     := k & (! ceil) & ( ( ! ( concrete | bytes   ) ) | symbolic | nobytes )
tangle_haskell  := k            & ( ( ! ( concrete | nobytes ) ) | symbolic | bytes   )

HOOK_NAMESPACES    = KRYPTO JSON
EXTRA_KOMPILE_OPTS =
KOMPILE_OPTS      += --hook-namespaces "$(HOOK_NAMESPACES)" -I $(KEVM_INCLUDE)/kframework -I $(INSTALL_INCLUDE)/kframework $(EXTRA_KOMPILE_OPTS)

ifneq (,$(RELEASE))
    KOMPILE_OPTS += -O2
endif

JAVA_KOMPILE_OPTS ?=

KOMPILE_JAVA := kompile --debug --backend java --md-selector "$(tangle_java)" \
                $(KOMPILE_OPTS) $(JAVA_KOMPILE_OPTS)

HASKELL_KOMPILE_OPTS ?=

KOMPILE_HASKELL := kompile --debug --backend haskell --md-selector "$(tangle_haskell)" \
                   $(KOMPILE_OPTS) $(HASKELL_KOMPILE_OPTS)

STANDALONE_KOMPILE_OPTS := -L$(LOCAL_LIB) -I$(K_INSTALL)/include/kllvm  \
                           $(PLUGIN_SUBMODULE)/plugin-c/plugin_util.cpp \
                           $(PLUGIN_SUBMODULE)/plugin-c/crypto.cpp      \
                           $(PLUGIN_SUBMODULE)/plugin-c/blake2.cpp      \
                           -g -std=c++14 -lff -lcryptopp -lsecp256k1    \
                           -lssl -lcrypto

ifeq ($(UNAME_S),Linux)
    STANDALONE_KOMPILE_OPTS += -lprocps
endif
ifeq ($(UNAME_S),Darwin)
    OPENSSL_ROOT := $(shell brew --prefix openssl)
    STANDALONE_KOMPILE_OPTS += -I/usr/local/include -L/usr/local/lib -I$(OPENSSL_ROOT)/include -L$(OPENSSL_ROOT)/lib
endif

KOMPILE_STANDALONE := kompile --debug --backend llvm --md-selector "$(tangle_concrete)" \
                      $(KOMPILE_OPTS)                \
                      $(addprefix -ccopt ,$(STANDALONE_KOMPILE_OPTS))

# Java

java_dir           := java
java_main_module   := ETHEREUM-SIMULATION
java_syntax_module := $(java_main_module)
java_main_file     := driver.md
java_main_filename := $(basename $(notdir $(java_main_file)))
java_kompiled      := $(java_dir)/$(java_main_filename)-kompiled/compiled.bin

$(KEVM_LIB)/$(java_kompiled): $(includes)
	$(KOMPILE_JAVA) $(java_main_file)                     \
	                --directory $(KEVM_LIB)/$(java_dir)   \
	                --main-module $(java_main_module)     \
	                --syntax-module $(java_syntax_module)

# Haskell

haskell_dir            := haskell
haskell_main_module    := ETHEREUM-SIMULATION
haskell_syntax_module  := $(haskell_main_module)
haskell_main_file      := driver.md
haskell_main_filename  := $(basename $(notdir $(haskell_main_file)))
haskell_kompiled       := $(haskell_dir)/$(haskell_main_filename)-kompiled/definition.kore

$(KEVM_LIB)/$(haskell_kompiled): $(includes)
	$(KOMPILE_HASKELL) $(haskell_main_file)                     \
	                   --directory $(KEVM_LIB)/$(haskell_dir)   \
	                   --main-module $(haskell_main_module)     \
	                   --syntax-module $(haskell_syntax_module)

# Standalone

llvm_dir           := llvm
llvm_main_module   := ETHEREUM-SIMULATION
llvm_syntax_module := $(llvm_main_module)
llvm_main_file     := driver.md
llvm_main_filename := $(basename $(notdir $(llvm_main_file)))
llvm_kompiled      := $(llvm_dir)/$(llvm_main_filename)-kompiled/interpreter

$(KEVM_LIB)/$(llvm_kompiled): $(includes) $(libff_out)
	$(KOMPILE_STANDALONE) $(llvm_main_file)                     \
	                      --directory $(KEVM_LIB)/$(llvm_dir)   \
	                      --main-module $(llvm_main_module)     \
	                      --syntax-module $(llvm_syntax_module)

# Installing
# ----------

install_bins := kevm

install_libs := $(haskell_kompiled) \
                $(llvm_kompiled)    \
                $(java_kompiled)    \
                kore-json.py        \
                kast-json.py        \
                release.md          \
                version

build_bins := $(install_bins)

build_libs := $(install_libs)

$(KEVM_BIN)/$(KEVM): $(KEVM)
	install -D $< $@

$(KEVM_LIB)/%.py: %.py
	install -D $< $@

$(KEVM_LIB)/version:
	@mkdir -p $(dir $@)
	echo $(KEVM_RELEASE_TAG) > $@

$(KEVM_LIB)/release.md: INSTALL.md
	@mkdir -p $(dir $@)
	echo "KEVM Release $(KEVM_RELEASE_TAG)"  > $@
	echo                                    >> $@
	cat INSTALL.md                          >> $@

build: $(patsubst %, $(KEVM_BIN)/%, $(install_bins)) $(patsubst %, $(KEVM_LIB)/%, $(install_libs))

build-haskell: $(KEVM_LIB)/$(haskell_kompiled) $(KEVM_BIN)/$(KEVM)
build-llvm:    $(KEVM_LIB)/$(llvm_kompiled)    $(KEVM_BIN)/$(KEVM)
build-java:    $(KEVM_LIB)/$(java_kompiled)    $(KEVM_BIN)/$(KEVM)

all_bin_sources := $(shell find $(KEVM_BIN) -type f                                                                                                                    | sed 's|^$(KEVM_BIN)/||')
all_lib_sources := $(shell find $(KEVM_LIB) -type f -not -path "$(KEVM_LIB)/llvm/driver-kompiled/dt/*" -not -path "$(KEVM_LIB)/kframework/share/kframework/pl-tutorial/*" | sed 's|^$(KEVM_LIB)/||')

install: $(patsubst %, $(INSTALL_BIN)/%, $(all_bin_sources)) \
         $(patsubst %, $(INSTALL_LIB)/%, $(all_lib_sources))

$(INSTALL_BIN)/%: $(KEVM_BIN)/%
	install -D $< $@

$(INSTALL_LIB)/%: $(KEVM_LIB)/%
	install -D $< $@

uninstall:
	rm -rf $(INSTALL_BIN)/kevm
	rm -rf $(INSTALL_LIB)/kevm

# Tests
# -----

TEST_CONCRETE_BACKEND := llvm
TEST_SYMBOLIC_BACKEND := java

TEST_OPTIONS :=
CHECK        := git --no-pager diff --no-index --ignore-all-space -R

KEVM_MODE     := NORMAL
KEVM_SCHEDULE := ISTANBUL
KEVM_CHAINID  := 1

KPROVE_MODULE  := VERIFICATION
KPROVE_OPTS    ?=

test-all: test-all-conformance test-prove test-interactive test-parse
test: test-conformance test-prove test-interactive test-parse

# Generic Test Harnesses

tests/ethereum-tests/VMTests/%: KEVM_MODE     = VMTESTS
tests/ethereum-tests/VMTests/%: KEVM_SCHEDULE = DEFAULT

tests/specs/mcd/functional-spec.k%: KPROVE_MODULE = FUNCTIONAL-SPEC-SYNTAX

tests/%.run: tests/%
	$(KEVM) interpret $(TEST_OPTIONS) --backend $(TEST_CONCRETE_BACKEND)                                               \
	    --mode $(KEVM_MODE) --schedule $(KEVM_SCHEDULE) --chainid $(KEVM_CHAINID)                                      \
	    $< > tests/$*.$(TEST_CONCRETE_BACKEND)-out                                                                     \
	    || $(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out tests/templates/output-success-$(TEST_CONCRETE_BACKEND).json
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.run-interactive: tests/%
	$(KEVM) run $(TEST_OPTIONS) --backend $(TEST_CONCRETE_BACKEND)                                                     \
	    --mode $(KEVM_MODE) --schedule $(KEVM_SCHEDULE) --chainid $(KEVM_CHAINID)                                      \
	    $< > tests/$*.$(TEST_CONCRETE_BACKEND)-out                                                                     \
	    || $(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out tests/templates/output-success-$(TEST_CONCRETE_BACKEND).json
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.run-expected: tests/% tests/%.expected
	$(KEVM) run $(TEST_OPTIONS) --backend $(TEST_CONCRETE_BACKEND)                                                     \
	    --mode $(KEVM_MODE) --schedule $(KEVM_SCHEDULE) --chainid $(KEVM_CHAINID)                                      \
	    $< > tests/$*.$(TEST_CONCRETE_BACKEND)-out                                                                     \
	    || $(CHECK) tests/$*.$(TEST_CONCRETE_BACKEND)-out tests/$*.expected
	rm -rf tests/$*.$(TEST_CONCRETE_BACKEND)-out

tests/%.parse: tests/%
	$(KEVM) kast $(TEST_OPTIONS) --backend $(TEST_CONCRETE_BACKEND) $< kast > $@-out
	$(CHECK) $@-out $@-expected
	rm -rf $@-out

tests/specs/benchmarks/%-spec.k.prove:             KPROVE_OPTS += --smt-prelude $(dir $@)evm.smt2
tests/specs/functional/lemmas-no-smt-spec.k.prove: KPROVE_OPTS += --haskell-backend-command "kore-exec --smt=none"

tests/%.prove: tests/%
	$(KEVM) prove $(TEST_OPTIONS) --backend $(TEST_SYMBOLIC_BACKEND) $< $(KPROVE_MODULE) --format-failures $(KPROVE_OPTS) \
	    --concrete-rules $(shell cat $(dir $@)concrete-rules.txt | tr '\n' ',')

tests/%.prove-dry-run: tests/%
	$(KEVM) prove $(TEST_OPTIONS) --backend haskell $< $(KPROVE_MODULE) --format-failures $(KPROVE_OPTS) --dry-run \
	    --concrete-rules $(shell cat $(dir $@)concrete-rules.txt | tr '\n' ',')

tests/%.search: tests/%
	$(KEVM) search $(TEST_OPTIONS) --backend $(TEST_SYMBOLIC_BACKEND) $< "<statusCode> EVMC_INVALID_INSTRUCTION </statusCode>" > $@-out
	$(CHECK) $@-out $@-expected
	rm -rf $@-out

tests/%.klab-prove: tests/%
	$(KEVM) klab-prove $(TEST_OPTIONS) --backend $(TEST_SYMBOLIC_BACKEND) $< $(KPROVE_MODULE) --format-failures $(KPROVE_OPTS) \
	    --concrete-rules $(shell cat $(dir $@)concrete-rules.txt | tr '\n' ',')

# Smoke Tests

smoke_tests_run=tests/ethereum-tests/VMTests/vmArithmeticTest/add0.json \
                tests/ethereum-tests/VMTests/vmIOandFlowOperations/pop1.json \
                tests/interactive/sumTo10.evm

smoke_tests_prove=tests/specs/erc20/ds/transfer-failure-1-a-spec.k

# Conformance Tests

tests/ethereum-tests/%.json: tests/ethereum-tests/make.timestamp

slow_conformance_tests    = $(shell cat tests/slow.$(TEST_CONCRETE_BACKEND))    # timeout after 20s
failing_conformance_tests = $(shell cat tests/failing.$(TEST_CONCRETE_BACKEND))

test-all-conformance: test-all-vm test-all-bchain
test-rest-conformance: test-rest-vm test-rest-bchain
test-slow-conformance: $(slow_conformance_tests:=.run)
test-failing-conformance: $(failing_conformance_tests:=.run)
test-conformance: test-vm test-bchain

all_vm_tests     = $(wildcard tests/ethereum-tests/VMTests/*/*.json)
quick_vm_tests   = $(filter-out $(slow_conformance_tests), $(all_vm_tests))
passing_vm_tests = $(filter-out $(failing_conformance_tests), $(quick_vm_tests))
rest_vm_tests    = $(filter-out $(passing_vm_tests), $(all_vm_tests))

test-all-vm: $(all_vm_tests:=.run)
test-rest-vm: $(rest_vm_tests:=.run)
test-vm: $(passing_vm_tests:=.run)

all_bchain_tests     = $(wildcard tests/ethereum-tests/BlockchainTests/GeneralStateTests/*/*.json)                            \
                       $(wildcard tests/ethereum-tests/LegacyTests/Constantinople/BlockchainTests/GeneralStateTests/*/*.json)
quick_bchain_tests   = $(filter-out $(slow_conformance_tests), $(all_bchain_tests))
passing_bchain_tests = $(filter-out $(failing_conformance_tests), $(quick_bchain_tests))
rest_bchain_tests    = $(filter-out $(passing_bchain_tests), $(all_bchain_tests))

test-all-bchain: $(all_bchain_tests:=.run)
test-rest-bchain: $(rest_bchain_tests:=.run)
test-bchain: $(passing_bchain_tests:=.run)

# Proof Tests

prove_specs_dir        := tests/specs
prove_failing_tests    := $(shell cat tests/failing-symbolic.$(TEST_SYMBOLIC_BACKEND))
prove_benchmarks_tests := $(filter-out $(prove_failing_tests), $(wildcard $(prove_specs_dir)/benchmarks/*-spec.k))
prove_functional_tests := $(filter-out $(prove_failing_tests), $(wildcard $(prove_specs_dir)/functional/*-spec.k))
prove_opcodes_tests    := $(filter-out $(prove_failing_tests), $(wildcard $(prove_specs_dir)/opcodes/*-spec.k))
prove_erc20_tests      := $(filter-out $(prove_failing_tests), $(wildcard $(prove_specs_dir)/erc20/*/*-spec.k))
prove_bihu_tests       := $(filter-out $(prove_failing_tests), $(wildcard $(prove_specs_dir)/bihu/*-spec.k))
prove_examples_tests   := $(filter-out $(prove_failing_tests), $(wildcard $(prove_specs_dir)/examples/*-spec.k))
prove_mcd_tests        := $(filter-out $(prove_failing_tests), $(wildcard $(prove_specs_dir)/mcd/*-spec.k))

test-prove: test-prove-benchmarks test-prove-functional test-prove-opcodes test-prove-erc20 test-prove-bihu test-prove-examples test-prove-mcd
test-prove-benchmarks: $(prove_benchmarks_tests:=.prove)
test-prove-functional: $(prove_functional_tests:=.prove)
test-prove-opcodes:    $(prove_opcodes_tests:=.prove)
test-prove-erc20:      $(prove_erc20_tests:=.prove)
test-prove-bihu:       $(prove_bihu_tests:=.prove)
test-prove-examples:   $(prove_examples_tests:=.prove)
test-prove-mcd:        $(prove_mcd_tests:=.prove)

test-failing-prove: $(prove_failing_tests:=.prove)

test-klab-prove: $(smoke_tests_prove:=.klab-prove)

haskell_dry_run_failing := $(shell cat tests/failing-symbolic.haskell-dry-run)
haskell_dry_run         := $(filter-out $(haskell_dry_run_failing), $(wildcard $(prove_specs_dir)/*-spec.k) $(wildcard $(prove_specs_dir)/*/*-spec.k) $(wildcard $(prove_specs_dir)/*/*/*-spec.k))

test-haskell-dry-run: $(haskell_dry_run:=.prove-dry-run)

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
	$(KEVM) help

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
