cmake_minimum_required (VERSION 3.4)

execute_process(COMMAND which kompile OUTPUT_VARIABLE KOMPILE_PATH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND dirname ${KOMPILE_PATH} OUTPUT_VARIABLE K_BIN
    OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND which llvm-kompile OUTPUT_VARIABLE LLVM_PATH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND dirname ${LLVM_PATH} OUTPUT_VARIABLE LLVM_BIN
    OUTPUT_STRIP_TRAILING_WHITESPACE)
set(K_LIB ${K_BIN}/../lib)
set(LLVM_LIB ${LLVM_BIN}/../lib)
list(APPEND CMAKE_MODULE_PATH "${K_LIB}/cmake/kframework")
list(APPEND CMAKE_MODULE_PATH "${LLVM_LIB}/cmake/kframework")
include(LLVMKompilePrelude)
project (KevmVm CXX)

set(KOMPILED_DIR $ENV{KEVM_LIB_ABS}/$ENV{node_dir}/$ENV{node_main_filename}-kompiled)
set(KOMPILE_USE_MAIN "library")
set(TARGET_NAME "kevm-vm")

link_directories(AFTER SYSTEM $ENV{LIBRARY_PATH})

add_executable(kevm-vm
	$ENV{NODE_DIR}/vm/init.cpp
	$ENV{NODE_DIR}/vm/main.cpp
	$ENV{NODE_DIR}/vm/vm.cpp
	$ENV{NODE_DIR}/vm/kevm/semantics.cpp
	$ENV{NODE_DIR}/plugin-c/blockchain.cpp
	$ENV{NODE_DIR}/plugin-c/world.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/blake2.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/crypto.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/plugin_util.cpp
	$ENV{LOCAL_LIB}/proto/proto/msg.pb.cc)

if(UNIX AND NOT APPLE)
	set(LINK_PROCPS procps)
endif()

target_include_directories(kevm-vm
	PUBLIC $ENV{PLUGIN_SUBMODULE}/plugin-c
	PUBLIC $ENV{LOCAL_LIB}/proto
	PUBLIC $ENV{NODE_DIR}/plugin-c
	PUBLIC $ENV{NODE_DIR}/vm
	PUBLIC $ENV{NODE_DIR}/vm/kevm
	PUBLIC ${CMAKE_SOURCE_DIR}/..
	PUBLIC $ENV{KEVM_LIB_ABS}/libff/include
    PUBLIC ${LLVM_BIN}/../include/kllvm)
target_compile_options(kevm-vm
	PUBLIC $ENV{LLVM_KOMPILE_OPTS}
    PUBLIC -Wall) # FIXME: Bring back -werror
target_link_libraries(kevm-vm
	ff protobuf gmp ${LINK_PROCPS} cryptopp secp256k1 crypto)
include(LLVMKompile)
