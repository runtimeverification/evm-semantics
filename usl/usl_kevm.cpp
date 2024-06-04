#include "usl_kevm.h"

#include <kllvm-c/kllvm-c.h>
#include <runtime/header.h>

#include <cassert>
#include <optional>

using namespace usl_kevm;

std::optional<network_t> network_{std::nullopt};

void usl_kevm::init_network(network_t network) {
  network_.emplace(std::move(network));
}

void usl_kevm::execute_transaction(const kevm_config_t &kevm_config,
                                   const block_t &block, const message_t &tx,
                                   result_t &result, substate_t &substate) {
  assert(network_.has_value());

  kllvm_init();
}
