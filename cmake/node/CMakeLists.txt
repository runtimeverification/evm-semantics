cmake_minimum_required (VERSION 3.4)

list(APPEND CMAKE_MODULE_PATH "$ENV{K_RELEASE}/cmake")
include(LLVMKompilePrelude)
project (KevmVm CXX)

set(KOMPILED_DIR $ENV{node_dir}/$ENV{MAIN_DEFN_FILE}-kompiled)
set(KOMPILE_USE_MAIN "library")
set(TARGET_NAME "kevm-vm")

add_executable(kevm-vm
	$ENV{PLUGIN_SUBMODULE}/vm-c/init.cpp
	$ENV{PLUGIN_SUBMODULE}/vm-c/main.cpp
	$ENV{PLUGIN_SUBMODULE}/vm-c/vm.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/blockchain.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/crypto.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/world.cpp
	$ENV{node_dir}/$ENV{MAIN_DEFN_FILE}-kompiled/plugin/proto/msg.pb.cc
	$ENV{PLUGIN_SUBMODULE}/vm-c/kevm/semantics.cpp)

if(UNIX AND NOT APPLE)
	set(LINK_PROCPS procps)
endif()

target_include_directories(kevm-vm
	PUBLIC $ENV{PLUGIN_SUBMODULE}/plugin-c
	PUBLIC $ENV{node_dir}/$ENV{MAIN_DEFN_FILE}-kompiled/plugin
	PUBLIC $ENV{PLUGIN_SUBMODULE}/vm-c
	PUBLIC $ENV{PLUGIN_SUBMODULE}/vm-c/kevm
	PUBLIC ${CMAKE_SOURCE_DIR}/..)
target_compile_options(kevm-vm
	PUBLIC $ENV{LLVM_KOMPILE_OPTS}
	PUBLIC -Wall -Werror)
target_link_libraries(kevm-vm
	ff protobuf gmp ${LINK_PROCPS} cryptopp secp256k1)
target_link_directories(kevm-vm
	PUBLIC $ENV{LIBRARY_PATH})

include(LLVMKompile)
