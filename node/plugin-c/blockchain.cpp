#include <gmp.h>
#include <map>
#include "proto/msg.pb.h"
#include "world.h"
#include "runtime/header.h"

using namespace org::kframework::kevm::extvm;

static std::map<std::string, std::unique_ptr<Account>> accounts;
static std::map<std::string, std::map<std::string, std::unique_ptr<StorageData>>> storage;
static std::map<std::string, std::unique_ptr<Code>> code;
static std::map<std::string, std::unique_ptr<Blockhash>> blockhash;

void clear_cache() {
  accounts.clear();
  storage.clear();
  code.clear();
  blockhash.clear();
}

static Account* get_account(mpz_t acctID) {
  std::string id(mpz_get_str(0, 10, acctID));
  Account* acct = accounts[id].get();
  if (!acct) {
    acct = World::get_account(of_z_width(20, acctID));
    accounts[id] = std::unique_ptr<Account>(acct);
  }
  return acct;
}

static StorageData* get_storage_data(mpz_t acctID, mpz_t index) {
  std::string id(mpz_get_str(0, 10, acctID));
  std::string idx(mpz_get_str(0, 10, index));
  StorageData *data = storage[id][idx].get();
  if (!data) {
    data = World::get_storage_data(of_z_width(20, acctID), of_z(index));
    storage[id][idx] = std::unique_ptr<StorageData>(data);
  }
  return data;
}

static Code* get_code(mpz_t acctID) {
  std::string id(mpz_get_str(0, 10, acctID));
  Code* c = code[id].get();
  if (!c) {
    c = World::get_code(of_z_width(20, acctID));
    code[id] = std::unique_ptr<Code>(c);
  }
  return c;
}

static Blockhash* get_blockhash(mpz_t offset) {
  std::string off(mpz_get_str(0, 10, offset));
  Blockhash* h = blockhash[off].get();
  if (!h) {
    h = World::get_blockhash(mpz_get_ui(offset));
    blockhash[off] = std::unique_ptr<Blockhash>(h);
  }
  return h;
}

extern "C" {

string* makeString(const char*, ssize_t);

mpz_ptr hook_BLOCKCHAIN_getBalance(mpz_t acctID) {
  Account *acct = get_account(acctID);
  return to_z_unsigned(acct->balance());
}

mpz_ptr hook_BLOCKCHAIN_getNonce(mpz_t acctID) {
  Account *acct = get_account(acctID);
  return to_z_unsigned(acct->nonce());
}

bool hook_BLOCKCHAIN_isCodeEmpty(mpz_t acctID) {
  Account *acct = get_account(acctID);
  return acct->codeempty();
}

mpz_ptr hook_BLOCKCHAIN_getStorageData(mpz_t acctID, mpz_t index) {
  StorageData *data = get_storage_data(acctID, index);
  return to_z(data->data());
}

string* hook_BLOCKCHAIN_getCode(mpz_t acctID) {
  Code *code = get_code(acctID);
  return makeString(code->code().c_str(), code->code().size());
}

mpz_ptr hook_BLOCKCHAIN_getBlockhash(mpz_t offset) {
  Blockhash *h = get_blockhash(offset);
  return to_z_unsigned(h->hash());
}

bool hook_BLOCKCHAIN_accountExists(mpz_t acctID) {
  Account *acct = get_account(acctID);
  return acct->balance().size() != 0 || acct->nonce().size() != 0;
}
}
