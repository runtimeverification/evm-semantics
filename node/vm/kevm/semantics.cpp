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

uint64_t get_schedule(mpz_ptr number, CallContext *ctx) {
  mpz_ptr petersburg = to_z(ctx->ethereumconfig().petersburgblocknumber());
  static uint32_t petersburg_tag = getTagForSymbolName("LblPETERSBURG'Unds'EVM{}");
  static uint32_t constantinople_tag = getTagForSymbolName("LblCONSTANTINOPLE'Unds'EVM{}");
  static uint32_t byzantium_tag = getTagForSymbolName("LblBYZANTIUM'Unds'EVM{}");
  static uint32_t spuriousDragon_tag = getTagForSymbolName("LblSPURIOUS'Unds'DRAGON'Unds'EVM{}");
  static uint32_t tangerineWhistle_tag = getTagForSymbolName("LblTANGERINE'Unds'WHISTLE'Unds'EVM{}");
  static uint32_t homestead_tag = getTagForSymbolName("LblHOMESTEAD'Unds'EVM{}");
  static uint32_t frontier_tag = getTagForSymbolName("LblFRONTIER'Unds'EVM{}");
  uint32_t tag;
  if (mpz_cmp(number, petersburg) >= 0) {
    tag = petersburg_tag;
  } else {
    mpz_ptr constantinople = to_z(ctx->ethereumconfig().constantinopleblocknumber());
    if (mpz_cmp(number, constantinople) >= 0) {
      tag = constantinople_tag;
    } else {
      mpz_ptr byzantium = to_z(ctx->ethereumconfig().byzantiumblocknumber());
      if (mpz_cmp(number, byzantium) >= 0) {
        tag = byzantium_tag;
      } else {
        mpz_ptr spuriousDragon = to_z(ctx->ethereumconfig().eip161blocknumber());
        if (mpz_cmp(number, spuriousDragon) >= 0) {
          tag = spuriousDragon_tag;
        } else {
          mpz_ptr tangerineWhistle = to_z(ctx->ethereumconfig().eip150blocknumber());
          if (mpz_cmp(number, tangerineWhistle) >= 0) {
            tag = tangerineWhistle_tag;
          } else {
            mpz_ptr homestead = to_z(ctx->ethereumconfig().homesteadblocknumber());
            if (mpz_cmp(number, homestead) >= 0) {
              tag = homestead_tag;
            } else {
              tag = frontier_tag;
            }
          }
        }
      }
    }
  }
  return (((uint64_t)tag) << 32) | 1;
}

input_data unpack_input(bool iscreate, std::string data) {
  input_data res;
  res.args = (block *)makeString(data.c_str(), data.size());
  res.code = makeString("");
  res.function = makeString("");
  return res;
}

uint32_t kcellInjTag = getTagForSymbolName("inj{SortEthereumSimulation{}, SortKItem{}}");
uint32_t unparseByteStack = getTagForSymbolName("LblunparseByteStack{}");
