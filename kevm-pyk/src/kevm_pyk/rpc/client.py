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

    def remove_node(self, *, foundry_out: Path, test: str, node: str) -> None:
        self._proxy.remove_node(
            foundry_out=str(foundry_out),
            test=test,
            node=node,
        )

    def simplify_node(
        self,
        *,
        foundry_out: Path,
        test: str,
        node: str,
        replace: bool = False,
        minimize: bool = True,
        bug_report: bool = False,
    ) -> str:
        return self._proxy.simplify_node(
            foundry_out=str(foundry_out),
            test=test,
            node=node,
            replace=replace,
            minimize=minimize,
            bug_report=bug_report,
        )

    def step_node(
        self,
        *,
        foundry_out: Path,
        test: str,
        node: str,
        repeat: int = 1,
        depth: int = 1,
        minimize: bool = True,
        bug_report: bool = False,
    ) -> None:
        self._proxy.step_node(
            foundry_out=str(foundry_out),
            test=test,
            node=node,
            repeat=repeat,
            depth=depth,
            minimize=minimize,
            bug_report=bug_report,
        )
