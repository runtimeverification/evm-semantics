from pathlib import Path
from typing import Any, Dict, Iterable, List, Tuple

from pyk.cli_utils import check_dir_path
from tinyrpc.dispatch import public

from ..foundry import (
    foundry_list,
    foundry_remove_node,
    foundry_section_edge,
    foundry_show,
    foundry_simplify_node,
    foundry_step_node,
)


class FoundryController:
    _foundry_out: Path

    def __init__(self, foundry_out: Path):
        check_dir_path(foundry_out)
        self._foundry_out = foundry_out

    @public
    def list(self) -> List[Dict[str, Any]]:
        stats = foundry_list(foundry_out=self._foundry_out)
        return [stat.dict for stat in stats]

    @public
    def show(
        self,
        *,
        test: str,
        nodes: Iterable[str] = (),
        node_deltas: Iterable[Tuple[str, str]],
        to_module: bool = False,
        minimize: bool = True,
    ) -> str:
        return foundry_show(
            foundry_out=self._foundry_out,
            test=test,
            nodes=nodes,
            node_deltas=node_deltas,
            to_module=to_module,
            minimize=minimize,
        )

    @public
    def remove_node(self, *, test: str, node: str) -> None:
        foundry_remove_node(
            foundry_out=self._foundry_out,
            test=test,
            node=node,
        )

    @public
    def simplify_node(
        self,
        *,
        test: str,
        node: str,
        replace: bool = False,
        minimize: bool = True,
        bug_report: bool = False,
    ) -> str:
        return foundry_simplify_node(
            foundry_out=self._foundry_out,
            test=test,
            node=node,
            replace=replace,
            minimize=minimize,
            bug_report=bug_report,
        )

    @public
    def step_node(
        self,
        *,
        test: str,
        node: str,
        repeat: int = 1,
        depth: int = 1,
        minimize: bool = True,
        bug_report: bool = False,
    ) -> None:
        foundry_step_node(
            foundry_out=self._foundry_out,
            test=test,
            node=node,
            repeat=repeat,
            depth=depth,
            minimize=minimize,
            bug_report=bug_report,
        )

    @public
    def section_edge(
        self,
        *,
        test: str,
        edge: Tuple[str, str],
        sections: int = 2,
        replace: bool = False,
        minimize: bool = True,
        bug_report: bool = False,
    ) -> None:
        foundry_section_edge(
            foundry_out=self._foundry_out,
            test=test,
            edge=edge,
            sections=sections,
            replace=replace,
            minimize=minimize,
            bug_report=bug_report,
        )
