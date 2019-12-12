cmake_minimum_required (VERSION 3.4)

list(APPEND CMAKE_MODULE_PATH "$ENV{K_RELEASE}/cmake")
include(LLVMKompilePrelude)
project (KevmClient CXX)

set(KOMPILED_DIR $ENV{web3_dir}/web3-kompiled)
set(KOMPILE_USE_MAIN "library")
set(TARGET_NAME "kevm-client")

add_executable(kevm-client
	$ENV{PLUGIN_SUBMODULE}/vm-c/init.cpp
	$ENV{PLUGIN_SUBMODULE}/client-c/main.cpp
	$ENV{PLUGIN_SUBMODULE}/client-c/json.cpp
	$ENV{PLUGIN_SUBMODULE}/client-c/HttpHandler.cpp
	$ENV{PLUGIN_SUBMODULE}/plugin-c/crypto.cpp)

if(UNIX AND NOT APPLE)
	set(LINK_PROCPS procps)
endif()

target_include_directories(kevm-client
	PUBLIC $ENV{PLUGIN_SUBMODULE}/plugin-c
	PUBLIC $ENV{PLUGIN_SUBMODULE}/vm-c
	PUBLIC $ENV{PLUGIN_SUBMODULE}/../proxygen/proxygen/_build/deps/include
	PUBLIC $ENV{PLUGIN_SUBMODULE}/../proxygen/proxygen/_build/include
	PUBLIC ${CMAKE_SOURCE_DIR}/..)
target_compile_options(kevm-client
	PUBLIC $ENV{LLVM_KOMPILE_OPTS}
	PUBLIC -Wall -Werror -Wno-unknown-warning-option)
target_link_libraries(kevm-client
	ff gmp ${LINK_PROCPS} cryptopp secp256k1 glog gflags double-conversion boost_system boost_thread boost_regex pthread iberty
	boost_filesystem boost_context boost_program_options ssl crypto event z sodium
	$ENV{PLUGIN_SUBMODULE}/../proxygen/proxygen/_build/deps/lib/libfolly.a
	$ENV{PLUGIN_SUBMODULE}/../proxygen/proxygen/_build/proxygen/lib/libproxygen.a
	$ENV{PLUGIN_SUBMODULE}/../proxygen/proxygen/_build/proxygen/httpserver/libproxygenhttpserver.a
	$ENV{PLUGIN_SUBMODULE}/../proxygen/proxygen/_build/deps/lib/libwangle.a
	$ENV{PLUGIN_SUBMODULE}/../proxygen/proxygen/_build/deps/lib/libfizz.a
)

include(LLVMKompile)
