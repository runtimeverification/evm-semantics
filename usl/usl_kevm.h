#ifndef USL_KEVM_H
#define USL_KEVM_H

#include <cstdint>
#include <ctime>
#include <optional>
#include <string>
#include <vector>

namespace usl_kevm {

// We use the std::uint64_t type as a place holder for various data types. The
// actual bitwidth can be found in a comment. The bitwidth is refered to as
// scalar for data types that are described as arbitrary natural numbers in the
// Ethereum yellow paper.

// Common data types
using bytes_t = std::string;
using account_nonce_t = std::uint64_t;   // u64
using ether_t = std::uint64_t;           // scalar (wei)
using gas_t = std::uint64_t;             // scalar
using hash_t = std::uint64_t;            // u256 (a keccak-256 hash)
using account_address_t = std::uint64_t; // u160
using storage_key_t = std::uint64_t;     // u256
using storage_value_t = std::uint64_t;   // u256
using chain_id_t = std::uint64_t; // scalar, equal to 1 for main Ethereum chain
using number_t = std::uint64_t; // scalar

// Ommer List
struct ommer_t {
  account_address_t ommer_address;
  number_t ommer_number;
};
using ommer_list_t = std::vector<ommer_t>;

// Block
using difficulty_t = std::uint64_t; // scalar, typically 0
using timestamp_t =
    std::time_t; // scalar, equal to reasonable output of Unix's time()
using mix_hash_t = std::uint64_t;    // RANDAO mix
using block_nonce_t = std::uint64_t; // u64
struct block_t {
  hash_t previous_hash;
  hash_t ommers_hash;
  account_address_t coinbase;
  hash_t state_root;
  hash_t transactions_root;
  hash_t receipts_root;
  bytes_t logs_bloom;
  difficulty_t difficulty;
  number_t number;
  gas_t gas_limit;
  gas_t gas_used;
  timestamp_t timestamp;
  bytes_t extra_data;
  mix_hash_t mix_hash;
  block_nonce_t block_nonce;
  ether_t base_fee;
  hash_t withdrawals_root;
  ommer_list_t ommer_block_headers;
};

// Account
struct account_t {
  account_address_t account_id;
  ether_t balance;
  bytes_t code;
  account_nonce_t nonce;
};

// Access List
using storage_key_list_t = std::vector<storage_key_t>;
struct access_pair_t {
  account_address_t account_id;
  storage_key_list_t storage_keys;
};
using access_list_t = std::vector<access_pair_t>;

// Transaction Type
enum class tx_type_t { LEGACY, ACCESS_LIST, DYNAMIC_FEE };
using tx_type_option_t = std::optional<tx_type_t>;

// Message
using account_address_option_t = std::optional<account_address_t>;
using sig_v_t = std::uint64_t;
struct message_t {
  account_nonce_t tx_nonce;
  ether_t tx_gas_price;
  gas_t tx_gas_limit;
  account_address_option_t to;
  ether_t value;
  sig_v_t sig_v;
  bytes_t sig_r;
  bytes_t sig_s;
  bytes_t data;
  access_list_t tx_access;
  chain_id_t tx_chain_id;
  ether_t tx_priority_fee;
  ether_t tx_max_fee;
  tx_type_option_t tx_type;
};

// Network Callbacks
using add_account_callback_t = void (*)(account_t);
using remove_account_callback_t = void (*)(account_address_t);

using get_account_balance_callback_t =
    std::optional<ether_t> (*)(account_address_t);
using set_account_balance_callback_t = void (*)(account_address_t, ether_t);

using get_account_code_callback_t =
    std::optional<bytes_t> (*)(account_address_t);
using set_account_code_callback_t = void (*)(account_address_t, bytes_t);

using get_account_nonce_callback_t =
    std::optional<account_nonce_t> (*)(account_address_t);
using set_account_nonce_callback_t = void (*)(account_address_t,
                                              account_nonce_t);

using get_account_storage_callback_t =
    std::optional<storage_value_t> (*)(account_address_t, storage_key_t);
using set_account_storage_callback_t = void (*)(account_address_t,
                                                storage_key_t, storage_value_t);

using get_account_orig_storage_callback_t =
    std::optional<storage_value_t> (*)(account_address_t, storage_key_t);
using set_account_orig_storage_callback_t = void (*)(account_address_t,
                                                     storage_key_t,
                                                     storage_value_t);

using get_blockhash_callback_t = hash_t (*)(size_t offset);

// Network
struct network_t {
  chain_id_t chain_id;
  add_account_callback_t add_account;
  remove_account_callback_t remove_account;
  get_account_balance_callback_t get_account_balance;
  set_account_balance_callback_t set_account_balance;
  get_account_code_callback_t get_account_code;
  set_account_code_callback_t set_account_code;
  get_account_nonce_callback_t get_account_nonce;
  set_account_nonce_callback_t set_account_nonce;
  get_account_storage_callback_t get_account_storage;
  set_account_storage_callback_t set_account_storage;
  get_account_orig_storage_callback_t get_account_orig_storage;
  set_account_orig_storage_callback_t set_account_orig_storage;
  get_blockhash_callback_t get_blockhash;
};

// Log
using log_topic_t = std::uint64_t; // u256 (char[32])
using log_topic_list_t = std::vector<log_topic_t>;
struct log_t {
  account_address_t account;
  log_topic_list_t topics;
  bytes_t data;
};
using log_list_t = std::vector<log_t>;

// Accessed Storage List
struct accessed_storage_t {
  account_address_t account_address;
  storage_key_t storage_key;
};
using accessed_storage_list_t = std::vector<accessed_storage_t>;

// Substate
using account_address_list_t = std::vector<account_address_t>;
struct substate_t {
  account_address_list_t self_destrcut;
  log_list_t log;
  account_address_list_t touched_accounts;
  ether_t refund;
  account_address_list_t accessed_accounts;
  accessed_storage_list_t accessed_storage;
};

// Status Code
enum class status_code_t {
  EVMC_REJECTED,
  EVMC_INTERNAL_ERROR,
  EVMC_SUCCESS,
  EVMC_REVERT,
  EVMC_FAILURE,
  EVMC_INVALID_INSTRUCTION,
  EVMC_UNDEFINED_INSTRUCTION,
  EVMC_OUT_OF_GAS,
  EVMC_BAD_JUMP_DESTINATION,
  EVMC_STACK_OVERFLOW,
  EVMC_STACK_UNDERFLOW,
  EVMC_CALL_DEPTH_EXCEEDED,
  EVMC_INVALID_MEMORY_ACCESS,
  EVMC_STATIC_MODE_VIOLATION,
  EVMC_PRECOMPILE_FAILURE,
  EVMC_NONCE_EXCEEDED
};

// Result
using status_code_option_t = std::optional<status_code_t>;
struct result_t {
  bytes_t output;
  status_code_option_t status_code;
};

// Schedule
enum class schedule_t {
  DEFAULT,
  FRONTIER,
  HOMESTEAD,
  TANGERINE_WHISTLE,
  SPURIOUS_DRAGON,
  BYZANTIUM,
  CONSTANTINOPLE,
  PETERSBURG,
  ISTANBUL,
  BERLIN,
  LONDON,
  MERGE,
  SHANGHAI
};

// APIs
void init_network(network_t network);

void execute_transaction(const schedule_t schedule, const block_t &block,
                         const message_t &tx, result_t &result,
                         log_list_t &log);

} // end namespace usl_kevm

#endif // USL_KEVM_H
