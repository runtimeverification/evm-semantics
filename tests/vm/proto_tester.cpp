#include <stdio.h>
#include <iostream>
#include <arpa/inet.h>

#include <google/protobuf/util/message_differencer.h>
#include "proto/msg.pb.h"

using namespace org::kframework::kevm::extvm;
using namespace google::protobuf::util;

class VMQueryReader {
public:
  VMQueryReader(const char *infile) {
    if (!(data = fopen(infile, "r"))) {
      perror(infile);
      exit(1);
    }
  }
  ~VMQueryReader() { fclose(data); }

  int ateof() { return feof(data); }

  const VMQuery &message() { return current; }

  bool next() {
    uint32_t len;

    fread(&len, 1, 4, data);

    if (feof(data)) {
      return false;
    }

    len = ntohl(len);
    std::string buf(len, '\000');
    fread(&buf[0], 1, len, data);

    current.Clear();
    if(!current.ParseFromString(buf)) {
      return false;
    }

    return true;
  }
private:
  FILE *data;
  VMQuery current;
};

int main(int argc, char *argv[]) {
  if (argc != 3) {
    fprintf(stderr, "Usage: %s <vm stream 1> <vm stream 2>\n", argv[0]);
    exit(1);
  }

  VMQueryReader expected(argv[1]);
  VMQueryReader out(argv[2]);

  std::string differences;
  MessageDifferencer diff;
  diff.set_repeated_field_comparison(MessageDifferencer::AS_SET);
  diff.ReportDifferencesToString(&differences);

  while (expected.next() && out.next()) {
    if (!diff.Compare(expected.message(), out.message())) {
      std::cerr << expected.message().DebugString() << std::endl;
      std::cerr << out.message().DebugString() << std::endl;
      std::cerr << differences << std::endl;
      return 1;
    }
  }

  return 0;
}

