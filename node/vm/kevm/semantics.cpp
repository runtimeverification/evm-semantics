#include "proto/msg.pb.h"
#include "runtime/header.h"
#include "semantics.h"
#include "world.h"
#include "vm.h"
#include "init.h"
#include <string>

using namespace org::kframework::kevm::extvm;

bool get_error(mpz_ptr status) {
  return mpz_sgn(status) == 0;
}

std::string get_output_data(string **sptr) {
  string* s = *sptr;
  return std::string(s->data, len(s));
}

#define HEADER(tag) ((((uint64_t)(tag)) << 32) | 1)

uint64_t get_schedule(mpz_ptr number, CallContext *ctx) {
  static uint64_t berlin_tag           = HEADER(getTagForSymbolName("LblBERLIN'Unds'EVM{}"));
  static uint64_t istanbul_tag         = HEADER(getTagForSymbolName("LblISTANBUL'Unds'EVM{}"));
  static uint64_t petersburg_tag       = HEADER(getTagForSymbolName("LblPETERSBURG'Unds'EVM{}"));
  static uint64_t constantinople_tag   = HEADER(getTagForSymbolName("LblCONSTANTINOPLE'Unds'EVM{}"));
  static uint64_t byzantium_tag        = HEADER(getTagForSymbolName("LblBYZANTIUM'Unds'EVM{}"));
  static uint64_t spuriousDragon_tag   = HEADER(getTagForSymbolName("LblSPURIOUS'Unds'DRAGON'Unds'EVM{}"));
  static uint64_t tangerineWhistle_tag = HEADER(getTagForSymbolName("LblTANGERINE'Unds'WHISTLE'Unds'EVM{}"));
  static uint64_t homestead_tag        = HEADER(getTagForSymbolName("LblHOMESTEAD'Unds'EVM{}"));
  static uint64_t frontier_tag         = HEADER(getTagForSymbolName("LblFRONTIER'Unds'EVM{}"));

  mpz_ptr blockNum = to_z(ctx->ethereumconfig().berlinblocknumber());
  if (mpz_cmp(number, blockNum) >= 0) {
    return berlin_tag;
  }
  blockNum = to_z(ctx->ethereumconfig().istanbulblocknumber());
  if (mpz_cmp(number, blockNum) >= 0) {
    return istanbul_tag;
  }
  blockNum = to_z(ctx->ethereumconfig().petersburgblocknumber());
  if (mpz_cmp(number, blockNum) >= 0) {
    return petersburg_tag;
  }
  blockNum = to_z(ctx->ethereumconfig().constantinopleblocknumber());
  if (mpz_cmp(number, blockNum) >= 0) {
    return constantinople_tag;
  }
  blockNum = to_z(ctx->ethereumconfig().byzantiumblocknumber());
  if (mpz_cmp(number, blockNum) >= 0) {
    return byzantium_tag;
  }
  blockNum = to_z(ctx->ethereumconfig().eip161blocknumber());
  if (mpz_cmp(number, blockNum) >= 0) {
    return spuriousDragon_tag;
  }
  blockNum = to_z(ctx->ethereumconfig().eip150blocknumber());
  if (mpz_cmp(number, blockNum) >= 0) {
    return tangerineWhistle_tag;
  }
  blockNum = to_z(ctx->ethereumconfig().homesteadblocknumber());
  if (mpz_cmp(number, blockNum) >= 0) {
    return homestead_tag;
  }
  return frontier_tag;
}

input_data unpack_input(bool iscreate, std::string data) {
  input_data res;
  res.args = (block *)makeString(data.c_str(), data.size());
  res.code = makeString("");
  res.function = makeString("");
  return res;
}

uint32_t zinjTag = getTagForSymbolName("inj{SortInt{}, SortKItem{}}");
uint32_t unparseByteStack = getTagForSymbolName("LblunparseByteStack{}");
