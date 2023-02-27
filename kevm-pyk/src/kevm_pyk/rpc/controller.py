from pathlib import Path
from typing import Iterable, Tuple

from tinyrpc.dispatch import public

from ..foundry import foundry_show


class FoundryController:
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
