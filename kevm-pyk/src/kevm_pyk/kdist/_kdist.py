from __future__ import annotations

import concurrent.futures
import json
import logging
import shutil
from concurrent.futures import ProcessPoolExecutor
from contextlib import contextmanager
from dataclasses import dataclass
from graphlib import CycleError, TopologicalSorter
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING, final

from filelock import SoftFileLock
from pyk.utils import hash_str
from xdg_base_dirs import xdg_cache_home

from . import utils
from ._cache import target_cache
from .api import TargetId

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator, Mapping
    from concurrent.futures import Future
    from typing import Any, Final

    from filelock import FileLock

    from ._cache import CachedTarget


_LOGGER: Final = logging.getLogger(__name__)


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
            target_id = target_cache().resolve(target_id).id
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
        dep_ids = target_cache().resolve_deps(target_ids)
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
                    print(result, flush=True)
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
        target = target_cache().resolve(target_id)
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
        return {dep_fqn: self._target_dir(target_cache().resolve(dep_fqn).id) for dep_fqn in target.target.deps()}

    def _manifest(self, target: CachedTarget, args: dict[str, Any]) -> dict[str, Any]:
        res = target.target.manifest()
        res['args'] = dict(args)
        res['deps'] = {
            dep_fqn: utils.timestamp(self._manifest_file(target_cache().resolve(dep_fqn).id))
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
