from __future__ import annotations

import re
from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import TYPE_CHECKING, final

from . import utils

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator, Mapping
    from pathlib import Path
    from typing import Any


_ID_PATTERN = re.compile('[a-z0-9]+(-[a-z0-9]+)*')


def valid_id(s: str) -> bool:
    return _ID_PATTERN.fullmatch(s) is not None


@final
@dataclass(frozen=True)
class TargetId:
    plugin_name: str
    target_name: str

    def __init__(self, plugin_name: str, target_name: str):
        if not valid_id(plugin_name):
            raise ValueError(f'Invalid plugin name: {plugin_name!r}')

        if not valid_id(target_name):
            raise ValueError(f'Invalid target name: {target_name!r}')

        object.__setattr__(self, 'plugin_name', plugin_name)
        object.__setattr__(self, 'target_name', target_name)

    def __iter__(self) -> Iterator[str]:
        yield self.plugin_name
        yield self.target_name

    @staticmethod
    def parse(fqn: str) -> TargetId:
        segments = fqn.split('.')
        if len(segments) != 2:
            raise ValueError(f'Expected fully qualified target name, got: {fqn!r}')

        plugin_name, target_name = segments
        return TargetId(plugin_name, target_name)

    @property
    def full_name(self) -> str:
        return f'{self.plugin_name}.{self.target_name}'


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
