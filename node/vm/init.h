#ifndef INIT_H
#define INIT_H

#include <netinet/in.h>
#include "runtime/header.h"
#include <gmp.h>

extern "C" {
  void initStaticObjects(void);
  size_t hook_LIST_size_long(list *l);
  block* hook_LIST_get_long(list *l, size_t i);
  list hook_MAP_values(map *m);
  list hook_MAP_keys_list(map *m);
  block* hook_MAP_lookup(map *m, block* key);
  map hook_MAP_element(block*, block*);
  map hook_MAP_update(map *, block*, block*);
  block* take_steps(uint32_t, block*);
  string* makeString(const char *, ssize_t len=-1);
  string *hook_STRING_int2string(mpz_ptr);
}

int init(int port, in_addr host);
block *configvar(const char *name);

struct kseq {
  blockheader h;
  block* hd;
  uint64_t tl;
};

struct zinj {
  blockheader h;
  mpz_ptr data;
};

struct mapinj {
  blockheader h;
  map data;
};

struct inj {
  blockheader h;
  block* data;
};

struct stringinj {
  blockheader h;
  string *data;
};

typedef struct boolinj {
  struct blockheader h;
  bool data;
} boolinj;

struct jsonlist {
  blockheader h;
  block *hd;
  jsonlist* tl;
};

struct json {
  blockheader h;
  jsonlist *data;
};

struct jsonmember {
  blockheader h;
  block *key;
  block *val;
};

#endif
