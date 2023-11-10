from __future__ import annotations

import functools
from distutils.dir_util import copy_tree
from typing import TYPE_CHECKING, overload

from pyk.kbuild.utils import sync_files
from pyk.utils import run_process

from .. import config
from ..kompile import KompileTarget, kevm_kompile
from . import api as kdist

if TYPE_CHECKING:
    from collections.abc import Callable, Iterable, Mapping
    from pathlib import Path
    from typing import Any

    from .api import Builder


def _kevm_builder(kompile_args: Callable[[], Mapping[str, Any]]) -> Builder:
    @functools.wraps(kompile_args)
    def build(output_dir: Path, deps: dict[str, Path], args: dict[str, Any]) -> None:
        verbose = args.get('verbose', False)
        enable_llvm_debug = args.get('enable_llvm_debug', False)

        kevm_kompile(
            output_dir=output_dir,
            enable_llvm_debug=enable_llvm_debug,
            verbose=verbose,
            plugin_dir=deps.get('evm-semantics.plugin'),
            **kompile_args(),
        )

    return build


@overload
def kevm_target(kompile_args: Callable[[], Mapping[str, Any]]) -> None:
    ...


@overload
def kevm_target(*, deps: Iterable[str] = ...) -> Callable[[Callable[[], Mapping[str, Any]]], None]:
    ...


def kevm_target(
    kompile_args: Callable[[], Mapping[str, Any]] | None = None,
    *,
    deps: Iterable[str] = (),
) -> Callable[[Callable[[], Mapping[str, Any]]], None] | None:
    def decorator(kompile_args: Callable[[], Mapping[str, Any]]) -> None:
        return kdist.target(deps=deps)(_kevm_builder(kompile_args))

    if kompile_args is None:
        return decorator

    decorator(kompile_args)
    return None


@kevm_target(deps=('evm-semantics.plugin',))
def llvm() -> Mapping[str, Any]:
    return {
        'target': KompileTarget.LLVM,
        'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
        'optimization': 2,
    }


@kevm_target
def haskell() -> Mapping[str, Any]:
    return {
        'target': KompileTarget.HASKELL,
        'main_file': config.EVM_SEMANTICS_DIR / 'edsl.md',
        'main_module': 'EDSL',
        'syntax_module': 'EDSL',
    }


@kevm_target
def haskell_standalone() -> Mapping[str, Any]:
    return {
        'target': KompileTarget.HASKELL,
        'main_file': config.EVM_SEMANTICS_DIR / 'driver.md',
        'main_module': 'ETHEREUM-SIMULATION',
        'syntax_module': 'ETHEREUM-SIMULATION',
    }


@kdist.target
def plugin(output_dir: Path, deps: dict[str, Any], args: dict[str, Any]) -> None:
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
