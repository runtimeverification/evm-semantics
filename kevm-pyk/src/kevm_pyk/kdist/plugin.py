from __future__ import annotations

from contextlib import contextmanager
from distutils.dir_util import copy_tree
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import TYPE_CHECKING

from pyk.kbuild.utils import sync_files
from pyk.utils import run_process

from .. import config
from ..kompile import KompileTarget, kevm_kompile
from . import Target

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping
    from typing import Any, Final


class KEVMTarget(Target):
    _kompile_args: dict[str, Any]

    def __init__(self, kompile_args: Mapping[str, Any]):
        self._kompile_args = dict(kompile_args)

    def build(self, output_dir: Path, args: dict[str, Any]) -> None:
        verbose = args.get('verbose', False)
        enable_llvm_debug = args.get('enable_llvm_debug', False)

        kevm_kompile(
            output_dir=output_dir,
            enable_llvm_debug=enable_llvm_debug,
            verbose=verbose,
            **self._kompile_args,
        )


class PluginTarget(Target):
    def build(self, output_dir: Path, args: dict[str, Any]) -> None:
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

        with self._build_env() as build_dir:
            run_process(
                ['make', 'libcryptopp', 'libff', 'libsecp256k1', '-j3'],
                cwd=build_dir,
                pipe_stdout=not verbose,
            )
            copy_tree(str(build_dir / 'build/libcryptopp'), str(output_dir / 'libcryptopp'))
            copy_tree(str(build_dir / 'build/libff'), str(output_dir / 'libff'))
            copy_tree(str(build_dir / 'build/libsecp256k1'), str(output_dir / 'libsecp256k1'))

    @contextmanager
    def _build_env(self) -> Iterator[Path]:
        with TemporaryDirectory(prefix='evm-semantics-plugin-') as build_dir_str:
            build_dir = Path(build_dir_str)
            copy_tree(str(config.PLUGIN_DIR), str(build_dir))
            yield build_dir


__TARGETS__: Final = {
    'llvm': KEVMTarget(
        {
            'target': KompileTarget.LLVM,
            'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
            'main_module': 'ETHEREUM-SIMULATION',
            'syntax_module': 'ETHEREUM-SIMULATION',
            'optimization': 2,
        },
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
    'foundry': KEVMTarget(
        {
            'target': KompileTarget.HASKELL,
            'main_file': config.EVM_SEMANTICS_DIR / 'foundry.md',
            'main_module': 'FOUNDRY',
            'syntax_module': 'FOUNDRY',
        },
    ),
    'plugin': PluginTarget(),
}
