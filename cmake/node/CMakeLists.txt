cmake_minimum_required (VERSION 3.4)

if(APPLE)
  if(DEFINED ENV{HOMEBREW_PREFIX})
    set(BREW_PREFIX $ENV{HOMEBREW_PREFIX})
  else()
    execute_process(
      COMMAND brew --prefix
      OUTPUT_VARIABLE BREW_PREFIX
      ERROR_VARIABLE BREW_ERROR
      RESULT_VARIABLE BREW_RESULT
      OUTPUT_STRIP_TRAILING_WHITESPACE)

    if(NOT BREW_RESULT EQUAL 0)
      message(WARNING "Error running brew --prefix; you may need to manually configure package search paths.")
      message(WARNING "  : ${BREW_ERROR}")
    endif() # BREW_RESULT
  endif() # ENV{HOMEBREW_PREFIX}

  message(STATUS "Looking for Homebrew dependencies in ${BREW_PREFIX}")
  include_directories(AFTER SYSTEM "${BREW_PREFIX}/include")
  link_directories(AFTER "${BREW_PREFIX}/lib")
endif() # APPLE

execute_process(COMMAND which kompile OUTPUT_VARIABLE KOMPILE_PATH
    OUTPUT_STRIP_TRAILING_WHITESPACE)
execute_process(COMMAND dirname ${KOMPILE_PATH} OUTPUT_VARIABLE K_BIN
    OUTPUT_STRIP_TRAILING_WHITESPACE)
set(K_LIB ${K_BIN}/../lib)
list(APPEND CMAKE_MODULE_PATH "${K_LIB}/cmake/kframework")
include(LLVMKompilePrelude)
project (KevmVm CXX)

set(KOMPILED_DIR $ENV{KEVM_LIB_ABS}/$ENV{node_dir})
set(KOMPILE_USE_MAIN "library")
set(TARGET_NAME "kevm-vm")

link_directories(AFTER SYSTEM
  $ENV{LIBRARY_PATH}
  $ENV{KEVM_LIB_ABS}/libff/lib
  $ENV{KEVM_LIB_ABS}/libcryptopp/lib
  $ENV{KEVM_LIB_ABS}/libsecp256k1/lib)

if(APPLE)
  link_directories(AFTER SYSTEM "${BREW_PREFIX}/opt/openssl/lib")
endif()

add_executable(kevm-vm
  $ENV{NODE_DIR}/vm/init.cpp
  $ENV{NODE_DIR}/vm/main.cpp
  $ENV{NODE_DIR}/vm/vm.cpp
  $ENV{NODE_DIR}/vm/kevm/semantics.cpp
  $ENV{NODE_DIR}/plugin-c/blockchain.cpp
  $ENV{NODE_DIR}/plugin-c/world.cpp
  $ENV{PLUGIN_FULL_PATH}/plugin-c/blake2.cpp
  $ENV{PLUGIN_FULL_PATH}/plugin-c/crypto.cpp
  $ENV{PLUGIN_FULL_PATH}/plugin-c/plugin_util.cpp
  $ENV{LOCAL_LIB}/proto/proto/msg.pb.cc)

if(UNIX AND NOT APPLE)
  set(LINK_PROCPS procps)
endif()

if (APPLE)
  target_include_directories(kevm-vm
    PUBLIC "${BREW_PREFIX}/opt/openssl/include")
endif()

target_include_directories(kevm-vm
  PUBLIC $ENV{PLUGIN_FULL_PATH}/plugin-c
  PUBLIC $ENV{LOCAL_LIB}/proto
  PUBLIC $ENV{NODE_DIR}/plugin-c
  PUBLIC $ENV{NODE_DIR}/vm
  PUBLIC $ENV{NODE_DIR}/vm/kevm
  PUBLIC ${CMAKE_SOURCE_DIR}/..
  PUBLIC $ENV{KEVM_LIB_ABS}/libff/include
  PUBLIC $ENV{KEVM_LIB_ABS}/libcryptopp/include
  PUBLIC $ENV{KEVM_LIB_ABS}/libsecp256k1/include
  PUBLIC ${K_LIB}/../include/kllvm)
target_compile_options(kevm-vm
  PUBLIC $ENV{LLVM_KOMPILE_OPTS}
  PUBLIC -Wall -Werror -Wno-unused-result)
target_link_libraries(kevm-vm
  ff protobuf gmp ${LINK_PROCPS} cryptopp secp256k1 crypto)

include(LLVMKompile)
