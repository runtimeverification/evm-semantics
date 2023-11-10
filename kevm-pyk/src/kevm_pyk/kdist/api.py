from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Any


class Target(ABC):
    @abstractmethod
    def build(self, output_dir: Path, deps: dict[str, Path], args: dict[str, Any]) -> None:
        ...

    @abstractmethod
    def deps(self) -> Iterable[str]:
        ...
