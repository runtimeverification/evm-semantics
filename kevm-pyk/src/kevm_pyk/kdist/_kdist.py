from __future__ import annotations

import concurrent.futures
import logging
import os
import re
import shutil
from collections.abc import Mapping
from concurrent.futures import ProcessPoolExecutor
from contextlib import contextmanager
from graphlib import CycleError, TopologicalSorter
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING, NamedTuple

from filelock import SoftFileLock
from pyk.utils import check_dir_path, hash_str
from xdg_base_dirs import xdg_cache_home

import kevm_pyk

from .api import Target

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from concurrent.futures import Future
    from types import ModuleType
    from typing import Any, Final

    from filelock import FileLock


_LOGGER: Final = logging.getLogger(__name__)


_ID_PATTERN = re.compile('[a-z0-9]+(-[a-z0-9]+)*')


def _valid_id(s: str) -> bool:
    return _ID_PATTERN.fullmatch(s) is not None


def _dist_dir() -> Path:
    dist_dir_env = os.getenv('KEVM_DIST_DIR')  # Used by Nix flake to set the output
    if dist_dir_env:
        return Path(dist_dir_env).resolve()

    module_dir = Path(kevm_pyk.__file__).parent
    digest = hash_str({'module-dir': module_dir})[:7]
    return xdg_cache_home() / f'kdist-{digest}'


def _plugins() -> dict[str, dict[str, Target]]:
    import importlib
    from importlib.metadata import entry_points

    plugins = entry_points(group='kdist')

    res: dict[str, dict[str, Target]] = {}
    for plugin in plugins:
        plugin_name = plugin.name

        if not _valid_id(plugin_name):
            _LOGGER.warning(f'Invalid plugin name, skipping: {plugin_name}')
            continue

        _LOGGER.info(f'Loading kdist plugin: {plugin_name}')
        module_name = plugin.value
        try:
            _LOGGER.info(f'Importing module: {module_name}')
            module = importlib.import_module(module_name)
        except Exception:
            _LOGGER.error(f'Module {module_name} cannot be imported', exc_info=True)
            continue

        res[plugin_name] = _load_targets(module)

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

        if not _valid_id(key):
            _LOGGER.warning(f'Invalid target name (in {module.__name__}): {key}')
            continue

        if not isinstance(value, Target):
            _LOGGER.warning(f'Invalid target value in {module.__name__} for key {key}: {value!r}')
            continue

        res[key] = value

    return res


_DIST_DIR: Final = _dist_dir()
_PLUGINS: Final = _plugins()


class TargetId(NamedTuple):
    plugin: str
    target: str

    @property
    def fqn(self) -> str:
        return f'{self.plugin}.{self.target}'

    @property
    def dir(self) -> Path:
        return _DIST_DIR / self.plugin / self.target


def plugins() -> dict[str, list[str]]:
    return {plugin: list(targets) for plugin, targets in _PLUGINS.items()}


def targets() -> list[str]:
    return [TargetId(plugin, target).fqn for plugin, targets in plugins().items() for target in targets]


def which(target_fqn: str | None = None) -> Path:
    if target_fqn:
        return _resolve(target_fqn).dir
    return _DIST_DIR


def clean(target_fqn: str | None = None) -> Path:
    res = which(target_fqn)
    shutil.rmtree(res, ignore_errors=True)
    return res


def get(target_fqn: str) -> Path:
    res = which(target_fqn)
    if not res.exists():
        raise ValueError(f'Target is not built: {target_fqn}')
    return res


def get_or_none(target_fqn: str) -> Path | None:
    res = which(target_fqn)
    if not res.exists():
        return None
    return res


def build(
    target_fqns: list[str],
    *,
    jobs: int = 1,
    force: bool = False,
    enable_llvm_debug: bool = False,
    verbose: bool = False,
) -> None:
    deps = _resolve_deps(target_fqns)
    target_graph = TopologicalSorter(deps)
    try:
        target_graph.prepare()
    except CycleError as err:
        raise RuntimeError(f'Cyclic dependencies found: {err.args[1]}') from err

    deps_fqns = [target.fqn for target in deps]
    _LOGGER.info(f"Building targets: {', '.join(deps_fqns)}")

    with ProcessPoolExecutor(max_workers=jobs) as pool:
        pending: dict[Future[Path], TargetId] = {}

        def submit(target_id: TargetId) -> None:
            future = pool.submit(
                _build_target,
                target_id=target_id,
                args={'enable_llvm_debug': enable_llvm_debug, 'verbose': verbose},
                force=force,
            )
            pending[future] = target_id

        for target_id in target_graph.get_ready():
            submit(target_id)

        while pending:
            done, _ = concurrent.futures.wait(pending, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                result = future.result()
                print(result)
                target_id = pending[future]
                target_graph.done(target_id)
                for new_target_id in target_graph.get_ready():
                    submit(new_target_id)
                pending.pop(future)


def _build_target(
    target_id: TargetId,
    args: dict[str, Any],
    *,
    force: bool = False,
) -> Path:
    output_dir = target_id.dir

    with _lock(target_id):
        if not force and output_dir.exists():
            return output_dir

        shutil.rmtree(output_dir, ignore_errors=True)
        output_dir.mkdir(parents=True)

        target = _resolve_id(target_id)
        deps = {target: which(target) for target in target.deps()}

        with (
            _build_dir(target_id) as build_dir,
            _cwd(build_dir),
        ):
            try:
                target.build(output_dir, deps=deps, args=args)
            except BaseException as err:
                shutil.rmtree(output_dir, ignore_errors=True)
                raise RuntimeError(f'Build failed: {target_id.fqn}') from err

        return output_dir


def _resolve(target_fqn: str) -> TargetId:
    segments = target_fqn.split('.')
    if len(segments) != 2:
        raise ValueError(f'Expected fully qualified target name, got: {target_fqn!r}')

    plugin, target = segments

    if not _valid_id(plugin):
        raise ValueError(f'Invalid plugin identifier: {plugin!r}')

    if not _valid_id(target):
        raise ValueError(f'Invalid target identifier: {target!r}')

    _plugins = plugins()

    try:
        targets = _plugins[plugin]
    except KeyError:
        raise ValueError(f'Undefined plugin: {plugin}') from None

    if not target in targets:
        raise ValueError(f'Plugin {plugin} does not define target: {target}')

    return TargetId(plugin, target)


def _resolve_id(target_id: TargetId) -> Target:
    plugin, target = target_id
    return _PLUGINS[plugin][target]


def _resolve_deps(target_fqns: Iterable[str]) -> dict[TargetId, list[TargetId]]:
    res: dict[TargetId, list[TargetId]] = {}
    pending = [_resolve(target_fqn) for target_fqn in target_fqns]
    while pending:
        target_id = pending.pop()
        if target_id in res:
            continue
        target = _resolve_id(target_id)
        deps = [_resolve(target_fqn) for target_fqn in target.deps()]
        res[target_id] = deps
        pending += deps
    return res


def _lock(target_id: TargetId) -> FileLock:
    lock_file = target_id.dir.with_suffix('.lock')
    lock_file.parent.mkdir(parents=True, exist_ok=True)
    return SoftFileLock(lock_file)


@contextmanager
def _build_dir(target_id: TargetId) -> Iterator[Path]:
    tmp_dir_prefix = f'kdist-{target_id.plugin}-{target_id.target}-'
    with TemporaryDirectory(prefix=tmp_dir_prefix) as build_dir_str:
        build_dir = Path(build_dir_str)
        yield build_dir


@contextmanager
def _cwd(path: Path) -> Iterator[None]:
    check_dir_path(path)
    old_cwd = os.getcwd()
    os.chdir(str(path))
    yield
    os.chdir(old_cwd)
