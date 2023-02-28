from pathlib import Path
from typing import Iterable, List, Tuple

from tinyrpc import RPCClient, RPCProxy
from tinyrpc.protocols.jsonrpc import JSONRPCProtocol
from tinyrpc.transports.http import HttpPostClientTransport

from ..foundry import CfgStat


class FoundryClient:
    _proxy: RPCProxy

    def __init__(self, host: str, port: int):
        protocol = JSONRPCProtocol()
        transport = HttpPostClientTransport(f'http://{host}:{port}')
        client = RPCClient(protocol, transport)
        self._proxy = client.get_proxy()

    def list(self, *, foundry_out: Path) -> List[CfgStat]:
        dcts = self._proxy.list(foundry_out=str(foundry_out))
        return [CfgStat.from_dict(dct) for dct in dcts]

    def show(
        self,
        *,
        foundry_out: Path,
        test: str,
        nodes: Iterable[str] = (),
        node_deltas: Iterable[Tuple[str, str]] = (),
        to_module: bool = False,
        minimize: bool = True,
    ) -> str:
        return self._proxy.show(
            foundry_out=str(foundry_out),
            test=test,
            nodes=nodes,
            node_deltas=node_deltas,
            to_module=to_module,
            minimize=minimize,
        )
