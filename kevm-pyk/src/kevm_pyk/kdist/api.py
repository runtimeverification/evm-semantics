from __future__ import annotations

from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, final

from . import utils

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from pathlib import Path
    from typing import Any


class Target(ABC):
    @abstractmethod
    def build(self, output_dir: Path, deps: dict[str, Path], args: dict[str, Any], verbose: bool) -> None:
        ...

    def deps(self) -> Iterable[str]:
        return ()

    def source(self) -> Iterable[str | Path]:
        return ()

    def context(self) -> Mapping[str, str]:
        return {}

    @final
    def manifest(self) -> dict[str, Any]:
        source = {}
        package_path = utils.package_path(self)
        source_files = [file.resolve() for source in self.source() for file in utils.files_for_path(source)]
        for source_file in source_files:
            try:
                file_id = str(source_file.relative_to(package_path))
            except ValueError as err:
                raise ValueError(f'Source file is not within package: {source_file}') from err
            source[file_id] = utils.timestamp(source_file)

        context = dict(self.context())
        return {'context': context, 'source': source}
