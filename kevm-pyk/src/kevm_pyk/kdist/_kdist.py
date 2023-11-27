from __future__ import annotations

import concurrent.futures
import json
import logging
import re
import shutil
from collections.abc import Mapping
from concurrent.futures import ProcessPoolExecutor
from contextlib import contextmanager
from dataclasses import dataclass
from graphlib import CycleError, TopologicalSorter
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING, NamedTuple, final

from filelock import SoftFileLock
from pyk.utils import hash_str
from xdg_base_dirs import xdg_cache_home

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


@final
@dataclass(frozen=True)
class TargetId:
    plugin_name: str
    target_name: str

    def __init__(self, plugin_name: str, target_name: str):
        if not _valid_id(plugin_name):
            raise ValueError(f'Invalid plugin name: {plugin_name!r}')

        if not _valid_id(target_name):
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

    def resolve(self, target_id: str | TargetId) -> CachedTarget:
        if isinstance(target_id, str):
            target_id = TargetId.parse(target_id)

        plugin_name, target_name = target_id
        try:
            targets = self._plugins[plugin_name]
        except KeyError:
            raise ValueError(f'Undefined plugin: {plugin_name}') from None

        try:
            res = targets[target_name]
        except KeyError:
            raise ValueError(f'Plugin {plugin_name} does not define target: {target_name}') from None

        return res

    def resolve_deps(self, target_ids: Iterable[str | TargetId]) -> dict[TargetId, list[TargetId]]:
        res: dict[TargetId, list[TargetId]] = {}
        pending = [self.resolve(target_id) for target_id in target_ids]
        while pending:
            target = pending.pop()
            if target.id in res:
                continue
            deps = [self.resolve(target_fqn) for target_fqn in target.target.deps()]
            res[target.id] = [dep.id for dep in deps]
            pending += deps
        return res

    @property
    def target_ids(self) -> list[TargetId]:
        return [target.id for plugin_name, targets in self._plugins.items() for target_name, target in targets.items()]

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


_CACHE: Final = TargetCache.load()


def target_ids() -> list[TargetId]:
    return _CACHE.target_ids


@final
@dataclass(frozen=True)
class KDist:
    kdist_dir: Path

    def __init__(self, kdist_dir: str | Path | None):
        if kdist_dir is None:
            kdist_dir = KDist.default_dir()
        kdist_dir = Path(kdist_dir).resolve()
        object.__setattr__(self, 'kdist_dir', kdist_dir)

    @staticmethod
    def default_dir() -> Path:
        import kevm_pyk

        module_dir = Path(kevm_pyk.__file__).parent
        digest = hash_str({'module-dir': module_dir})[:7]
        return xdg_cache_home() / f'kdist-{digest}'

    def which(self, target_id: str | TargetId | None = None) -> Path:
        if target_id:
            target_id = _CACHE.resolve(target_id).id
            return self._target_dir(target_id)
        return self.kdist_dir

    def clean(self, target_id: str | TargetId | None = None) -> Path:
        res = self.which(target_id)
        shutil.rmtree(res, ignore_errors=True)
        return res

    def get(self, target_id: str | TargetId) -> Path:
        res = self.which(target_id)
        if not res.exists():
            if isinstance(target_id, TargetId):
                target_id = target_id.full_name
            raise ValueError(f'Target is not built: {target_id}')
        return res

    def get_or_none(self, target_id: str | TargetId) -> Path | None:
        res = self.which(target_id)
        if not res.exists():
            return None
        return res

    def build(
        self,
        target_ids: Iterable[str | TargetId],
        *,
        args: Mapping[str, str] | None = None,
        jobs: int = 1,
        force: bool = False,
        verbose: bool = False,
    ) -> None:
        args = dict(args) if args else {}
        dep_ids = _CACHE.resolve_deps(target_ids)
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
                    self._build_target,
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

    # Helpers

    def _build_target(
        self,
        target_id: TargetId,
        args: dict[str, Any],
        *,
        force: bool,
        verbose: bool,
    ) -> Path:
        target = _CACHE.resolve(target_id)
        output_dir = self._target_dir(target_id)
        manifest_file = self._manifest_file(target_id)

        with self._lock(target_id):
            manifest = self._manifest(target, args)

            if not force and self._up_to_date(target_id, manifest):
                return output_dir

            shutil.rmtree(output_dir, ignore_errors=True)
            output_dir.mkdir(parents=True)
            manifest_file.unlink(missing_ok=True)

            with (
                self._build_dir(target_id) as build_dir,
                utils.cwd(build_dir),
            ):
                try:
                    target.target.build(output_dir, deps=self._deps(target), args=args, verbose=verbose)
                except BaseException as err:
                    shutil.rmtree(output_dir, ignore_errors=True)
                    raise RuntimeError(f'Build failed: {target_id.full_name}') from err

            manifest_file.write_text(json.dumps(manifest))
            return output_dir

    def _target_dir(self, target_id: TargetId) -> Path:
        return self.kdist_dir / target_id.plugin_name / target_id.target_name

    def _manifest_file(self, target_id: TargetId) -> Path:
        return self.kdist_dir / target_id.plugin_name / f'{target_id.target_name}.json'

    def _deps(self, target: CachedTarget) -> dict[str, Path]:
        return {dep_fqn: self._target_dir(_CACHE.resolve(dep_fqn).id) for dep_fqn in target.target.deps()}

    def _manifest(self, target: CachedTarget, args: dict[str, Any]) -> dict[str, Any]:
        res = target.target.manifest()
        res['args'] = dict(args)
        res['deps'] = {
            dep_fqn: utils.timestamp(self._manifest_file(_CACHE.resolve(dep_fqn).id))
            for dep_fqn in target.target.deps()
        }
        return res

    def _up_to_date(self, target_id: TargetId, new_manifest: dict[str, Any]) -> bool:
        if not self._target_dir(target_id).exists():
            return False
        manifest_file = self._manifest_file(target_id)
        if not manifest_file.exists():
            return False
        old_manifest = json.loads(manifest_file.read_text())
        return new_manifest == old_manifest

    def _lock(self, target_id: TargetId) -> FileLock:
        lock_file = self._target_dir(target_id).with_suffix('.lock')
        lock_file.parent.mkdir(parents=True, exist_ok=True)
        return SoftFileLock(lock_file)

    @contextmanager
    def _build_dir(self, target_id: TargetId) -> Iterator[Path]:
        tmp_dir_prefix = f'kdist-{target_id.plugin_name}-{target_id.target_name}-'
        with TemporaryDirectory(prefix=tmp_dir_prefix) as build_dir_str:
            build_dir = Path(build_dir_str)
            yield build_dir
