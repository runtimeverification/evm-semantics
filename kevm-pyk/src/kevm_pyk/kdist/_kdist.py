from __future__ import annotations

import concurrent.futures
import logging
import os
import shutil
from collections.abc import Mapping
from concurrent.futures import ProcessPoolExecutor
from graphlib import CycleError, TopologicalSorter
from pathlib import Path
from typing import TYPE_CHECKING

from filelock import SoftFileLock
from pyk.utils import hash_str
from xdg_base_dirs import xdg_cache_home

import kevm_pyk

from .api import Target

if TYPE_CHECKING:
    from collections.abc import Iterable
    from concurrent.futures import Future
    from types import ModuleType
    from typing import Any, Final

    from filelock import FileLock


_LOGGER: Final = logging.getLogger(__name__)


def _dist_dir() -> Path:
    dist_dir_env = os.getenv('KEVM_DIST_DIR')  # Used by Nix flake to set the output
    if dist_dir_env:
        return Path(dist_dir_env).resolve()

    module_dir = Path(kevm_pyk.__file__).parent
    digest = hash_str({'module-dir': module_dir})[:7]
    return xdg_cache_home() / f'kdist-{digest}'


def _targets() -> dict[str, Target]:
    import importlib
    from importlib.metadata import entry_points

    plugins = entry_points(group='kdist')

    res: dict[str, Target] = {}
    for plugin in plugins:
        _LOGGER.info(f'Loading kdist plugin: {plugin.name}')
        module_name = plugin.value
        try:
            _LOGGER.info(f'Importing module: {module_name}')
            module = importlib.import_module(module_name)
        except Exception:
            _LOGGER.error(f'Module {module_name} cannot be imported', exc_info=True)
            continue

        targets = _load_targets(module)

        # TODO Namespaces
        for key, value in targets.items():
            if key in res:
                _LOGGER.warning(f'Target with key already defined, skipping: {key} (in {module_name})')
                continue

            res[key] = value

    return res


def _load_targets(module: ModuleType) -> dict[str, Target]:
    if not hasattr(module, '__TARGETS__'):
        _LOGGER.warning(f'Module does not define __TARGETS__: {module.__name__}')
        return {}

    targets = module.__TARGETS__

    if not isinstance(targets, Mapping):
        _LOGGER.warning(f'Invalid __TARGETS__ attribute: {module.__name__}')
        return {}

    res: dict[str, Target] = {}
    for key, value in targets.items():
        if not isinstance(key, str):
            _LOGGER.warning(f'Invalid target key in {module.__name__}: {key!r}')
            continue

        if not isinstance(value, Target):
            _LOGGER.warning(f'Invalid target value in {module.__name__} for key {key}: {value!r}')
            continue

        res[key] = value

    return res


_DIST_DIR: Final = _dist_dir()
_TARGETS: Final = _targets()


def targets() -> list[str]:
    return list(_TARGETS)


def check(target: str) -> None:
    if target not in _TARGETS:
        raise ValueError(f'Undefined target: {target}')


def which(target: str | None = None) -> Path:
    if target:
        check(target)
        return _DIST_DIR / target
    return _DIST_DIR


def clean(target: str | None = None) -> Path:
    res = which(target)
    shutil.rmtree(res, ignore_errors=True)
    return res


def get(target: str) -> Path:
    res = which(target)
    if not res.exists():
        raise ValueError(f'Target is not built: {target}')
    return res


def get_or_none(target: str) -> Path | None:
    res = which(target)
    if not res.exists():
        return None
    return res


def build(
    targets: list[str],
    *,
    jobs: int = 1,
    force: bool = False,
    enable_llvm_debug: bool = False,
    verbose: bool = False,
) -> None:
    deps = _resolve_deps(targets)
    target_graph = TopologicalSorter(deps)
    try:
        target_graph.prepare()
    except CycleError as err:
        raise RuntimeError(f'Cyclic dependencies found: {err.args[1]}') from err

    _LOGGER.info(f"Building targets: {', '.join(deps)}")

    with ProcessPoolExecutor(max_workers=jobs) as pool:
        pending: dict[Future[Path], str] = {}

        def submit(target: str) -> None:
            future = pool.submit(
                _build_target,
                target=target,
                args={'enable_llvm_debug': enable_llvm_debug, 'verbose': verbose},
                force=force,
            )
            pending[future] = target

        for target in target_graph.get_ready():
            submit(target)

        while pending:
            done, _ = concurrent.futures.wait(pending, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                result = future.result()
                print(result)
                target = pending[future]
                target_graph.done(target)
                for new_target in target_graph.get_ready():
                    submit(new_target)
                pending.pop(future)


def _resolve_deps(targets: Iterable[str]) -> dict[str, list[str]]:
    res: dict[str, list[str]] = {}
    pending = list(targets)
    while pending:
        target_name = pending.pop()
        if target_name in res:
            continue
        target = _resolve(target_name)
        deps = list(target.deps())
        res[target_name] = deps
        pending += deps
    return res


def _resolve(target: str) -> Target:
    check(target)
    return _TARGETS[target]


def _build_target(
    target: str,
    args: dict[str, Any],
    *,
    force: bool = False,
) -> Path:
    output_dir = which(target)

    with _lock(target):
        if not force and output_dir.exists():
            return output_dir

        shutil.rmtree(output_dir, ignore_errors=True)
        output_dir.mkdir(parents=True)

        _target = _TARGETS[target]
        deps = {target: which(target) for target in _target.deps()}

        try:
            _target.build(output_dir, deps=deps, args=args)
        except BaseException as err:
            shutil.rmtree(output_dir, ignore_errors=True)
            raise RuntimeError(f'Build failed: {target}') from err

        return output_dir


def _lock(target: str) -> FileLock:
    lock_file = which(target).with_suffix('.lock')
    lock_file.parent.mkdir(parents=True, exist_ok=True)
    return SoftFileLock(lock_file)
