from __future__ import annotations

import inspect
import re
from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Protocol, overload

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable
    from pathlib import Path
    from typing import Any


class Builder(Protocol):
    def __call__(self, output_dir: Path, deps: dict[str, Path], args: dict[str, Any]) -> None:
        ...


class Target(ABC):
    @abstractmethod
    def build(self, output_dir: Path, deps: dict[str, Path], args: dict[str, Any]) -> None:
        ...

    @abstractmethod
    def deps(self) -> Iterable[str]:
        ...

    @staticmethod
    def from_builder(builder: Builder, deps: Iterable[str] = ()) -> Target:
        class _Target(Target):
            def build(self, output_dir: Path, deps: dict[str, Path], args: dict[str, Any]) -> None:
                return builder(output_dir, deps, args)

            def deps(self) -> tuple[str, ...]:
                return tuple(deps)

        return _Target()


@overload
def target(builder: Builder) -> None:
    ...


@overload
def target(*, name: str | None = ..., deps: Iterable[str] = ...) -> Callable[[Builder], None]:
    ...


# TODO logging
# TODO validate target_name
def target(
    builder: Builder | None = None,
    *,
    name: str | None = None,
    deps: Iterable[str] = (),
) -> Callable[[Builder], None] | None:
    caller_frame = inspect.stack()[1].frame
    module_globals = caller_frame.f_globals
    module_name = module_globals['__name__']

    def decorator(builder: Builder) -> None:
        if '__TARGETS__' not in module_globals:
            module_globals['__TARGETS__'] = {}

        targets = module_globals['__TARGETS__']

        target_name = name if name else _builder_to_target_name(builder)
        if target_name in targets:
            raise ValueError(f'Target is already defined in {module_name}: {target_name}')

        targets[target_name] = Target.from_builder(builder, deps)

    # @target(...)
    if builder is None:
        return decorator

    # @target
    decorator(builder)
    return None


def _builder_to_target_name(builder: Any) -> str:
    name = builder.__name__
    name = re.sub(r'_+', '-', name).lower()
    name = name.removeprefix('-')
    name = name.removesuffix('-')
    return name
