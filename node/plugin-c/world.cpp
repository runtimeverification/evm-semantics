#include <cstdint>
#include <iostream>
#include <gmp.h>
#include <arpa/inet.h>
#include "proto/msg.pb.h"
#include "world.h"
#include "runtime/header.h"

using namespace org::kframework::kevm::extvm;

extern "C" {
  string* hook_BYTES_int2bytes(mpz_t, mpz_t, uint64_t);
  mpz_ptr hook_BYTES_bytes2int(string*, uint64_t, uint64_t);
  uint64_t tag_big_endian();
  uint64_t tag_unsigned();
  string* makeString(const char*, ssize_t);
}

std::string of_z_width(unsigned width, mpz_ptr i) {
  mpz_t len;
  mpz_init_set_ui(len, width);
  string* token = hook_BYTES_int2bytes(len, i, tag_big_endian());
  mpz_clear(len);
  return std::string(token->data, len(token));
}

std::string of_z(mpz_ptr i) {
  if (mpz_sgn(i) == 0) {
    return std::string("\000", 1);
  }
  size_t bits = mpz_sizeinbase(i, 2);
  size_t width = (bits + 8) / 8;
  mpz_t len;
  mpz_init_set_ui(len, width);
  string* token = hook_BYTES_int2bytes(len, i, tag_big_endian());
  mpz_clear(len);
  return std::string(token->data, len(token));
}

mpz_ptr to_z_unsigned(std::string str) {
  string* token = makeString(str.c_str(), str.size());
  return hook_BYTES_bytes2int(token, tag_big_endian(), tag_unsigned());
}

mpz_ptr to_z(std::string str) {
  string* token = makeString(str.c_str(), str.size());
  return hook_BYTES_bytes2int(token, tag_big_endian(), 0);
}

FILE *vm_out_chan;
FILE *vm_in_chan;

template<typename Cls>
Cls* send_query(VMQuery q, Cls* output) {
  std::cerr << q.DebugString() << std::endl;
  std::string buf;
  q.SerializeToString(&buf);
  uint32_t len = htonl(buf.size());
  fwrite((char *)&len, 4, 1, vm_out_chan);
  fwrite(buf.c_str(), 1, buf.length(), vm_out_chan);
  fflush(vm_out_chan);
  fread((char *)&len, 4, 1, vm_in_chan);
  len = ntohl(len);
  std::string buf2(len, '\000');
  fread(&buf2[0], 1, len, vm_in_chan);
  output->ParseFromString(buf2);
  std::cerr << output->DebugString() << std::endl;
  return output;
}

Account* World::get_account(std::string acct) {
  GetAccount get;
  get.set_address(acct);
  VMQuery q;
  *q.mutable_getaccount() = get;
  return send_query(q, new Account());
}

StorageData *World::get_storage_data(std::string acct, std::string index) {
  GetStorageData get;
  get.set_address(acct);
  get.set_offset(index);
  VMQuery q;
  *q.mutable_getstoragedata() = get;
  return send_query(q, new StorageData());
}

Code* World::get_code(std::string acct) {
  GetCode get;
  get.set_address(acct);
  VMQuery q;
  *q.mutable_getcode() = get;
  return send_query(q, new Code());
}

Blockhash* World::get_blockhash(int offset) {
  GetBlockhash get;
  get.set_offset(offset);
  VMQuery q;
  *q.mutable_getblockhash() = get;
  return send_query(q, new Blockhash());
}

