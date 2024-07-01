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

void usl_kevm::execute_transaction(const schedule_t schedule,
                                   const block_t &block, const message_t &tx,
                                   result_t &result, log_list_t &log) {
  assert(network_.has_value());

  kllvm_init();
}
