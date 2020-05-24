cmake_minimum_required (VERSION 3.4)

list(APPEND CMAKE_MODULE_PATH "$ENV{K_RELEASE}/cmake")
list(APPEND CMAKE_MODULE_PATH "$ENV{K_RELEASE}/lib/cmake/kframework")
include(LLVMKompilePrelude)
project (KevmClient CXX)

set(KOMPILED_DIR $ENV{web3_dir}/$ENV{MAIN_DEFN_FILE}-kompiled)
set(KOMPILE_USE_MAIN "library")
set(TARGET_NAME "kevm-client")

add_executable(kevm-client
	$ENV{PLUGIN_SUBMODULE}/client-c/init.cpp
	$ENV{PLUGIN_SUBMODULE}/client-c/main.cpp
	$ENV{PLUGIN_SUBMODULE}/client-c/json.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/crypto.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/blake2.cpp)

if(UNIX AND NOT APPLE)
	set(LINK_PROCPS procps)
endif()

target_include_directories(kevm-client
	PUBLIC $ENV{PLUGIN_SUBMODULE}/plugin-c
	PUBLIC $ENV{PLUGIN_SUBMODULE}/deps/cpp-httplib
	PUBLIC $ENV{K_RELEASE}/include/kllvm
	PUBLIC ${CMAKE_SOURCE_DIR}/..)
target_compile_options(kevm-client
	PUBLIC $ENV{LLVM_KOMPILE_OPTS}
	PUBLIC -Wall -Werror -Wno-unknown-warning-option)
target_link_libraries(kevm-client
	ff gmp ${LINK_PROCPS} cryptopp secp256k1 gflags
)

include(LLVMKompile)
