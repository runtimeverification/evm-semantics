from __future__ import annotations

import logging
import time
from collections.abc import Mapping
from typing import TYPE_CHECKING, NamedTuple

from .api import Target, TargetId, valid_id

if TYPE_CHECKING:
    from collections.abc import Iterable
    from types import ModuleType
    from typing import Final


_LOGGER: Final = logging.getLogger(__name__)


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

            if not valid_id(plugin_name):
                _LOGGER.warning(f'Invalid plugin name, skipping: {plugin_name}')
                continue

            _LOGGER.info(f'Loading plugin: {plugin_name}')
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

            if not valid_id(target_name):
                _LOGGER.warning(f'Invalid target name (in {module.__name__}): {target_name}')
                continue

            if not isinstance(target, Target):
                _LOGGER.warning(f'Invalid target in {module.__name__} for name {target_name}: {target!r}')
                continue

            res[target_name] = CachedTarget(TargetId(plugin_name, target_name), target)

        return res


_TARGET_CACHE: TargetCache | None = None


def target_cache() -> TargetCache:
    global _TARGET_CACHE
    if not _TARGET_CACHE:
        _LOGGER.info('Loading target cache')
        start_time = time.time()
        _TARGET_CACHE = TargetCache.load()
        end_time = time.time()
        delta_time = end_time - start_time
        _LOGGER.info(f'Target cache loaded in {delta_time:.3f}s')
    return _TARGET_CACHE


def target_ids() -> list[TargetId]:
    return target_cache().target_ids
