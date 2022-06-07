#include <iostream>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <unistd.h>
#include "proto/msg.pb.h"
#include "runtime/alloc.h"
#include "version.h"
#include "init.h"

extern FILE *vm_out_chan;
extern FILE *vm_in_chan;

using namespace org::kframework::kevm::extvm;

CallResult run_transaction(CallContext ctx);

extern "C" {
  void freeAllKoreMem(void);
}

int init(int port, in_addr host);

int main(int argc, char **argv) {
  std::string usage = std::string("Usage: ") + argv[0] + " PORT BIND_ADDRESS";
  if (argc == 2 && argv[1] == std::string("--help")) {
    std::cout << usage << std::endl;
    return 0;
  } else if (argc == 2 && argv[1] == std::string("--version")) {
    std::cout << argv[0] << " version " << VM_VERSION << std::endl;
    return 0;
  } else if (argc != 3) {
    std::cerr << "Incorrect number of arguments" << std::endl;
    std::cerr << usage << std::endl;
    return 1;
  }
  int port = std::stoi(argv[1]);
  in_addr host;
  if (!inet_aton(argv[2], &host)) {
    std::cerr << "Invalid bind address" << std::endl;
    return 1;
  }

  int sock = init(port, host);

  sockaddr_in peer;
  while(1) {
    socklen_t len = sizeof(peer);
    int clientsock = accept(sock, (sockaddr *)&peer, &len);
    if (clientsock == -1) {
      perror("accept");
      return 1;
    }
    FILE *_if = fdopen(clientsock, "r");
    if (!_if) {
      perror("fdopen");
      return 1;
    }
    vm_in_chan = _if;

    FILE *of = fdopen(clientsock, "w");
    if (!of) {
      perror("fdopen");
      return 1;
    }
    vm_out_chan = of;

    (void)fread((char *)&len, 4, 1, _if);
    len = ntohl(len);
    std::string buf(len, '\000');
    (void)fread(&buf[0], 1, len, _if);
    Hello h;
    bool success = h.ParseFromString(buf);
    if (success && h.version() == "2.2") {
      while(1) {
        (void)fread((char *)&len, 4, 1, _if);
        if (feof(_if)) {
          break;
        }
        len = ntohl(len);
        std::string buf2(len, '\000');
        (void)fread(&buf2[0], len, 1, _if);
        if (feof(_if)) {
          break;
        }
        CallContext ctx;
        if (!ctx.ParseFromString(buf2)) {
          break;
        }
        CallResult result = run_transaction(ctx);
        freeAllKoreMem();
        VMQuery q;
        *q.mutable_callresult() = result;
        std::string buf3;
        q.SerializeToString(&buf3);
        len = htonl(buf3.size());
        fwrite((char *)&len, 4, 1, of);
        fwrite(buf3.c_str(), 1, buf3.length(), of);
        fflush(of);
      }
    } else if (success) {
      std::cerr << "Invalid protobuf version, found " << h.version() << std::endl;
    }
    if(shutdown(clientsock, SHUT_WR)) {
      perror("shutdown");
      return 1;
    }
    fclose(_if);
    fclose(of);
  }
}
