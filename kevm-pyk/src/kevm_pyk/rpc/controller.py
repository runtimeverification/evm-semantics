from pathlib import Path
from typing import Any, Dict, Iterable, List, Tuple

from tinyrpc.dispatch import public

from ..foundry import foundry_list, foundry_remove_node, foundry_show


class FoundryController:
    @public
    def list(self, *, foundry_out: str) -> List[Dict[str, Any]]:
        stats = foundry_list(foundry_out=Path(foundry_out))
        return [stat.dict for stat in stats]

    @public
    def show(
        self,
        *,
        foundry_out: str,
        test: str,
        nodes: Iterable[str] = (),
        node_deltas: Iterable[Tuple[str, str]],
        to_module: bool = False,
        minimize: bool = True,
    ) -> str:
        return foundry_show(
            foundry_out=Path(foundry_out),
            test=test,
            nodes=nodes,
            node_deltas=node_deltas,
            to_module=to_module,
            minimize=minimize,
        )

    @public
    def remove_node(self, *, foundry_out: str, test: str, node: str) -> None:
        foundry_remove_node(
            foundry_out=Path(foundry_out),
            test=test,
            node=node,
        )
