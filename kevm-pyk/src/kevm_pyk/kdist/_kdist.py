from __future__ import annotations

import concurrent.futures
import json
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
from pyk.utils import hash_str
from xdg_base_dirs import xdg_cache_home

import kevm_pyk

from . import utils
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


# TODO validate
class TargetId(NamedTuple):
    plugin: str
    target: str

    @staticmethod
    def parse(fqn: str) -> TargetId:
        segments = fqn.split('.')
        if len(segments) != 2:
            raise ValueError(f'Expected fully qualified target name, got: {fqn!r}')

        plugin, target = segments

        if not _valid_id(plugin):
            raise ValueError(f'Invalid plugin identifier: {plugin!r}')

        if not _valid_id(target):
            raise ValueError(f'Invalid target identifier: {target!r}')

        return TargetId(plugin, target)

    @property
    def full_name(self) -> str:
        return f'{self.plugin}.{self.target}'

    @property
    def dir(self) -> Path:
        return _DIST_DIR / self.plugin / self.target

    @property
    def manifest_file(self) -> Path:
        return _DIST_DIR / self.plugin / f'{self.target}.json'


class CachedTarget(NamedTuple):
    id: TargetId
    target: Target


class TargetCache:
    _plugins: dict[str, dict[str, CachedTarget]]

    def __init__(self, plugins: Mapping[str, Mapping[str, CachedTarget]]):
        _plugins: dict[str, dict[str, CachedTarget]] = {}
        for plugin_name, targets in plugins.items():
            _targets: dict[str, CachedTarget] = {}
            _plugins[plugin_name] = _targets
            for target_name, target in targets.items():
                _targets[target_name] = target
        self._plugins = _plugins

    def resolve(self, target_id: TargetId) -> CachedTarget:
        plugin, target = target_id
        try:
            targets = self._plugins[plugin]
        except KeyError:
            raise ValueError(f'Undefined plugin: {plugin}') from None

        try:
            res = targets[target]
        except KeyError:
            raise ValueError(f'Plugin {plugin} does not define target: {target}') from None

        return res

    def parse(self, fqn: str) -> TargetId:
        res = TargetId.parse(fqn)
        self.resolve(res)
        return res

    @property
    def target_ids(self) -> list[TargetId]:
        return [TargetId(plugin, target) for plugin, targets in self._plugins.items() for target in targets]

    @staticmethod
    def load() -> TargetCache:
        return TargetCache(TargetCache._load_plugins())

    @staticmethod
    def _load_plugins() -> dict[str, dict[str, CachedTarget]]:
        import importlib
        from importlib.metadata import entry_points

        plugins = entry_points(group='kdist')

        res: dict[str, dict[str, CachedTarget]] = {}
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

            res[plugin_name] = TargetCache._load_targets(plugin_name, module)

        return res

    @staticmethod
    def _load_targets(plugin_name: str, module: ModuleType) -> dict[str, CachedTarget]:
        if not hasattr(module, '__TARGETS__'):
            _LOGGER.warning(f'Module does not define __TARGETS__: {module.__name__}')
            return {}

        targets = module.__TARGETS__

        if not isinstance(targets, Mapping):
            _LOGGER.warning(f'Invalid __TARGETS__ attribute: {module.__name__}')
            return {}

        res: dict[str, CachedTarget] = {}
        for target_name, target in targets.items():
            if not isinstance(target_name, str):
                _LOGGER.warning(f'Invalid target name in {module.__name__}: {target_name!r}')
                continue

            if not _valid_id(target_name):
                _LOGGER.warning(f'Invalid target name (in {module.__name__}): {target_name}')
                continue

            if not isinstance(target, Target):
                _LOGGER.warning(f'Invalid target in {module.__name__} for name {target_name}: {target!r}')
                continue

            res[target_name] = CachedTarget(TargetId(plugin_name, target_name), target)

        return res


_DIST_DIR: Final = _dist_dir()
_CACHE: Final = TargetCache.load()


def plugins() -> dict[str, list[str]]:
    res: dict[str, list[str]] = {}
    for plugin, target in _CACHE.target_ids:
        targets = res.get(plugin, [])
        targets.append(target)
        res[plugin] = targets
    return res


def targets() -> list[str]:
    return [target_id.full_name for target_id in _CACHE.target_ids]


def which(target_fqn: str | None = None) -> Path:
    if target_fqn:
        return _CACHE.parse(target_fqn).dir
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
    args: Mapping[str, str] | None = None,
    jobs: int = 1,
    force: bool = False,
    verbose: bool = False,
) -> None:
    args = dict(args) if args else {}
    dep_ids = _resolve_deps(target_fqns)
    target_graph = TopologicalSorter(dep_ids)
    try:
        target_graph.prepare()
    except CycleError as err:
        raise RuntimeError(f'Cyclic dependencies found: {err.args[1]}') from err

    deps_fqns = [target_id.full_name for target_id in dep_ids]
    _LOGGER.info(f"Building targets: {', '.join(deps_fqns)}")

    with ProcessPoolExecutor(max_workers=jobs) as pool:
        pending: dict[Future[Path], TargetId] = {}

        def submit(target_id: TargetId) -> None:
            future = pool.submit(
                _build_target,
                target_id=target_id,
                args=args,
                force=force,
                verbose=verbose,
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
    force: bool,
    verbose: bool,
) -> Path:
    output_dir = target_id.dir

    with _lock(target_id):
        manifest = _manifest(target_id, args)

        if not force and _up_to_date(target_id, manifest):
            return output_dir

        shutil.rmtree(output_dir, ignore_errors=True)
        output_dir.mkdir(parents=True)
        target_id.manifest_file.unlink(missing_ok=True)

        target = _CACHE.resolve(target_id)
        deps = {target: which(target) for target in target.target.deps()}

        with (
            _build_dir(target_id) as build_dir,
            utils.cwd(build_dir),
        ):
            try:
                target.target.build(output_dir, deps=deps, args=args, verbose=verbose)
            except BaseException as err:
                shutil.rmtree(output_dir, ignore_errors=True)
                raise RuntimeError(f'Build failed: {target_id.full_name}') from err

        target_id.manifest_file.write_text(json.dumps(manifest))
        return output_dir


def _manifest(target_id: TargetId, args: dict[str, Any]) -> dict[str, Any]:
    target = _CACHE.resolve(target_id)
    res = target.target.manifest()
    res['args'] = dict(args)
    res['deps'] = {dep_fqn: utils.timestamp(_resolve(dep_fqn).manifest_file) for dep_fqn in target.target.deps()}
    return res


def _up_to_date(target_id: TargetId, new_manifest: dict[str, Any]) -> bool:
    if not target_id.dir.exists():
        return False
    if not target_id.manifest_file.exists():
        return False
    old_manifest = json.loads(target_id.manifest_file.read_text())
    return new_manifest == old_manifest


def _resolve(target_fqn: str) -> TargetId:
    res = TargetId.parse(target_fqn)
    plugin, target = res

    _plugins = plugins()

    try:
        targets = _plugins[plugin]
    except KeyError:
        raise ValueError(f'Undefined plugin: {plugin}') from None

    if not target in targets:
        raise ValueError(f'Plugin {plugin} does not define target: {target}')

    return res


def _resolve_deps(target_fqns: Iterable[str]) -> dict[TargetId, list[TargetId]]:
    res: dict[TargetId, list[TargetId]] = {}
    pending = [_CACHE.parse(target_fqn) for target_fqn in target_fqns]
    while pending:
        target_id = pending.pop()
        if target_id in res:
            continue
        target = _CACHE.resolve(target_id)
        deps = [_CACHE.parse(target_fqn) for target_fqn in target.target.deps()]
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
