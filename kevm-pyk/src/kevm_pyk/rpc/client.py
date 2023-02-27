from tinyrpc import RPCClient, RPCProxy
from tinyrpc.protocols.jsonrpc import JSONRPCProtocol
from tinyrpc.transports.http import HttpPostClientTransport


class FoundryClient:
    _proxy: RPCProxy

    def __init__(self, host: str, port: int):
        protocol = JSONRPCProtocol()
        transport = HttpPostClientTransport(f'http://{host}:{port}')
        client = RPCClient(protocol, transport)
        self._proxy = client.get_proxy()

    def hello(self) -> None:
        print(self._proxy.hello())
