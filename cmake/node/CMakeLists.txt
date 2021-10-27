cmake_minimum_required (VERSION 3.4)

execute_process(COMMAND which kompile OUTPUT_VARIABLE KOMPILE_PATH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND dirname ${KOMPILE_PATH} OUTPUT_VARIABLE K_BIN
    OUTPUT_STRIP_TRAILING_WHITESPACE)
set(K_LIB ${K_BIN}/../lib)
list(APPEND CMAKE_MODULE_PATH "${K_LIB}/cmake/kframework")

execute_process(COMMAND which llvm-kompile OUTPUT_VARIABLE LLVM_PATH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND dirname ${LLVM_PATH} OUTPUT_VARIABLE LLVM_BIN
    OUTPUT_STRIP_TRAILING_WHITESPACE)

find_program(CMAKE_C_COMPILER clang-8)
find_program(CMAKE_C_COMPILER clang-7)
find_program(CMAKE_C_COMPILER clang)
find_program(CMAKE_CXX_COMPILER clang++-8)
find_program(CMAKE_CXX_COMPILER clang++-7)
find_program(CMAKE_CXX_COMPILER clang++)
find_program(CMAKE_C_COMPILER_AR llvm-ar-8)
find_program(CMAKE_C_COMPILER_AR llvm-ar-7)
find_program(CMAKE_C_COMPILER_AR llvm-ar)
find_program(CMAKE_C_COMPILER_RANLIB llvm-ranlib-8)
find_program(CMAKE_C_COMPILER_RANLIB llvm-ranlib-7)
find_program(CMAKE_C_COMPILER_RANLIB llvm-ranlib)


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
    PUBLIC ${LLVM_BIN}/../include/kllvm) # FIXME: Include paths
target_compile_options(kevm-vm
	PUBLIC $ENV{LLVM_KOMPILE_OPTS}
    PUBLIC -Wall) # FIXME: Bring back -werror
target_link_libraries(kevm-vm
	ff protobuf gmp ${LINK_PROCPS} cryptopp secp256k1 crypto)

set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(CMAKE_AR "${CMAKE_C_COMPILER_AR}")
set(CMAKE_RANLIB "${CMAKE_C_COMPILER_RANLIB}")

find_program(LLVM_KOMPILE llvm-kompile)

set(LLVM_KOMPILE_FLAGS "${KOMPILED_DIR}/definition.kore ${KOMPILED_DIR}/dt ${KOMPILE_USE_MAIN}")
set(CMAKE_CXX_LINK_EXECUTABLE "${LLVM_KOMPILE} ${LLVM_KOMPILE_FLAGS} <FLAGS> <CMAKE_CXX_LINK_FLAGS> <LINK_FLAGS> <OBJECTS> -o <TARGET> <LINK_LIBRARIES>")

get_filename_component(K_BIN_DIR ${LLVM_KOMPILE} DIRECTORY)
include_directories(${K_BIN_DIR}/../include)

target_compile_options(${TARGET_NAME}
	PUBLIC -Wno-return-type-c-linkage)
set_target_properties(${TARGET_NAME} PROPERTIES LINK_DEPENDS "${KOMPILED_DIR}/definition.kore")

install(TARGETS ${TARGET_NAME}
	RUNTIME DESTINATION bin)

