from __future__ import annotations

from distutils.dir_util import copy_tree
from typing import TYPE_CHECKING

from pyk.kbuild.utils import sync_files
from pyk.utils import run_process

from .. import config
from ..kompile import KompileTarget, kevm_kompile
from .api import Target

if TYPE_CHECKING:
    from collections.abc import Iterable, Mapping
    from pathlib import Path
    from typing import Any, Final


class KEVMTarget(Target):
    _kompile_args: dict[str, Any]
    _deps: tuple[str, ...]

    def __init__(self, kompile_args: Mapping[str, Any], *, deps: Iterable[str] | None = None):
        self._kompile_args = dict(kompile_args)
        self._deps = tuple(deps) if deps is not None else ()

    def build(self, output_dir: Path, deps: dict[str, Path], args: dict[str, Any]) -> None:
        verbose = args.get('verbose', False)
        enable_llvm_debug = args.get('enable_llvm_debug', False)

        kevm_kompile(
            output_dir=output_dir,
            enable_llvm_debug=enable_llvm_debug,
            verbose=verbose,
            plugin_dir=deps.get('plugin'),
            **self._kompile_args,
        )

    def deps(self) -> tuple[str, ...]:
        return self._deps


class PluginTarget(Target):
    def build(self, output_dir: Path, deps: dict[str, Any], args: dict[str, Any]) -> None:
        verbose = args.get('verbose', False)

        sync_files(
            source_dir=config.PLUGIN_DIR / 'plugin-c',
            target_dir=output_dir / 'plugin-c',
            file_names=[
                'blake2.cpp',
                'blake2.h',
                'crypto.cpp',
                'plugin_util.cpp',
                'plugin_util.h',
            ],
        )

        copy_tree(str(config.PLUGIN_DIR), '.')
        run_process(
            ['make', 'libcryptopp', 'libff', 'libsecp256k1', '-j3'],
            pipe_stdout=not verbose,
        )

        copy_tree('./build/libcryptopp', str(output_dir / 'libcryptopp'))
        copy_tree('./build/libff', str(output_dir / 'libff'))
        copy_tree('./build/libsecp256k1', str(output_dir / 'libsecp256k1'))


__TARGETS__: Final = {
    'llvm': KEVMTarget(
        {
            'target': KompileTarget.LLVM,
            'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
            'main_module': 'ETHEREUM-SIMULATION',
            'syntax_module': 'ETHEREUM-SIMULATION',
            'optimization': 2,
        },
        deps=('plugin',),
    ),
    'haskell': KEVMTarget(
        {
            'target': KompileTarget.HASKELL,
            'main_file': config.EVM_SEMANTICS_DIR / 'edsl.md',
            'main_module': 'EDSL',
            'syntax_module': 'EDSL',
        },
    ),
    'haskell-standalone': KEVMTarget(
        {
            'target': KompileTarget.HASKELL,
            'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
            'main_module': 'ETHEREUM-SIMULATION',
            'syntax_module': 'ETHEREUM-SIMULATION',
        },
    ),
    'plugin': PluginTarget(),
}
