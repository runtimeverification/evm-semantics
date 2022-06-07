#ifndef VM_H
#define VM_H

extern "C" {
  mpz_ptr hook_BLOCKCHAIN_getBalance(mpz_ptr);
  mpz_ptr hook_BLOCKCHAIN_getNonce(mpz_ptr);
  mpz_ptr hook_BLOCKCHAIN_getStorageData(mpz_ptr, mpz_ptr);
  bool hook_BLOCKCHAIN_accountExists(mpz_ptr);
  bool hook_BLOCKCHAIN_isCodeEmpty(mpz_ptr);
}

void clear_cache(void);

struct account;

struct acctinj {
  blockheader h;
  account* data;
};

struct log;

struct loginj {
  blockheader h;
  struct log* data;
};

struct accounts {
  blockheader h;
  map data;
};

struct runvm {
  blockheader h;
  bool iscreate;
  mpz_ptr to;
  mpz_ptr from;
  string* code;
  block* args;
  mpz_ptr value;
  mpz_ptr gasprice;
  mpz_ptr gas;
  mpz_ptr beneficiary;
  mpz_ptr difficulty;
  mpz_ptr number;
  mpz_ptr gaslimit;
  mpz_ptr timestamp;
  string* function;
};

struct accesslist {
  blockheader h;
  set addresses;
  set storage;
  runvm* runvm_ptr;
};

struct storageloc {
  blockheader h;
  mpz_ptr address;
  mpz_ptr location;
};

#endif
