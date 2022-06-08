#ifndef SEMANTICS_H
#define SEMANTICS_H

struct json;
struct jsonlist;
struct stringinj;
struct zinj;
struct inj;
struct mapinj;

struct account {
  blockheader h;
  zinj* acctID;
  zinj* balance;
  inj* code;
  mapinj *storage;
  mapinj *origStorage;
  zinj *nonce;
};

struct log {
  blockheader h;
  mpz_ptr acct;
  list topics;
  block *data;
};

struct input_data {
  string* code;
  block* args;
  string* function;
};

struct accounts;

struct tx_result {
  blockheader h;
  string* rets;
  mpz_ptr gas;
  mpz_ptr refund;
  mpz_ptr status;
  set selfdestruct;
  list logs;
  accounts* accounts_ptr; 
  set touched;
  string* statuscode;
};

struct accesslist_result {
  blockheader h;
  set addresses;
  set locations;
};

std::string get_output_data(string**);

extern uint32_t zinjTag;
extern uint32_t unparseByteStack;

#define logData(log) log->data

#endif
