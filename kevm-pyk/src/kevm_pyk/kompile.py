from __future__ import annotations

import concurrent.futures
import logging
import sys
from enum import Enum
from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.ktool import TypeInferenceMode
from pyk.ktool.kompile import HaskellKompile, KompileArgs, LLVMKompile, LLVMKompileType, MaudeKompile

from . import config

if TYPE_CHECKING:
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Final

    from pyk.ktool.kompile import Kompile


_LOGGER: Final = logging.getLogger(__name__)


HOOK_NAMESPACES: Final = ('JSON', 'KRYPTO')


class KompileTarget(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    MAUDE = 'maude'

    @property
    def md_selector(self) -> str:
        match self:
            case self.LLVM:
                return 'k & ! symbolic'
            case self.HASKELL | self.MAUDE:
                return 'k & ! concrete'
            case _:
                raise AssertionError()


def kevm_kompile(
    target: KompileTarget,
    output_dir: Path,
    main_file: Path,
    *,
    main_module: str | None,
    syntax_module: str | None,
    includes: Iterable[Path] = (),
    emit_json: bool = True,
    read_only: bool = False,
    ccopts: Iterable[str] = (),
    optimization: int = 0,
    llvm_kompile_type: LLVMKompileType | None = None,
    enable_llvm_debug: bool = False,
    plugin_dir: Path | None = None,
    debug_build: bool = False,
    debug: bool = False,
    verbose: bool = False,
    type_inference_mode: str | TypeInferenceMode | None = None,
    ignore_warnings: Iterable[str] = (),
) -> Path:
    if plugin_dir is None:
        plugin_dir = kdist.get('evm-semantics.plugin')

    ccopts = list(ccopts) + lib_ccopts(plugin_dir, debug_build=debug_build) + _warning_ccopts()
    return run_kompile(
        target,
        output_dir,
        main_file,
        main_module=main_module,
        syntax_module=syntax_module,
        includes=includes,
        emit_json=emit_json,
        read_only=read_only,
        ccopts=ccopts,
        optimization=optimization,
        llvm_kompile_type=llvm_kompile_type,
        enable_llvm_debug=enable_llvm_debug,
        debug_build=debug_build,
        debug=debug,
        verbose=verbose,
        type_inference_mode=type_inference_mode,
        ignore_warnings=ignore_warnings,
    )


def run_kompile(
    target: KompileTarget,
    output_dir: Path,
    main_file: Path,
    *,
    main_module: str | None,
    syntax_module: str | None,
    includes: Iterable[Path] = (),
    emit_json: bool = True,
    read_only: bool = False,
    ccopts: Iterable[str] = (),
    optimization: int = 0,
    llvm_kompile_type: LLVMKompileType | None = None,
    enable_llvm_debug: bool = False,
    debug_build: bool = False,
    debug: bool = False,
    verbose: bool = False,
    type_inference_mode: str | TypeInferenceMode | None = None,
    ignore_warnings: Iterable[str] = (),
) -> Path:
    if type_inference_mode is None:
        type_inference_mode = TypeInferenceMode.SIMPLESUB

    include_dirs = tuple(includes) + config.INCLUDE_DIRS

    base_args = KompileArgs(
        main_file=main_file,
        main_module=main_module,
        syntax_module=syntax_module,
        include_dirs=include_dirs,
        md_selector=target.md_selector,
        hook_namespaces=HOOK_NAMESPACES,
        emit_json=emit_json,
        read_only=read_only,
    )

    kompile: Kompile
    kernel = sys.platform
    haskell_binary = kernel != 'darwin'

    match target:
        case KompileTarget.LLVM:
            kompile = LLVMKompile(
                base_args=base_args,
                ccopts=ccopts,
                opt_level=optimization,
                llvm_kompile_type=llvm_kompile_type,
                enable_llvm_debug=enable_llvm_debug,
            )
            return kompile(
                output_dir=output_dir,
                debug=debug,
                verbose=verbose,
                type_inference_mode=type_inference_mode,
                ignore_warnings=ignore_warnings,
            )

        case KompileTarget.MAUDE:
            kompile_maude = MaudeKompile(
                base_args=base_args,
            )
            kompile_haskell = HaskellKompile(base_args=base_args)

            maude_dir = output_dir / 'kompiled-maude'

            def _kompile_maude() -> None:
                kompile_maude(
                    output_dir=maude_dir, debug=debug, verbose=verbose, type_inference_mode=type_inference_mode
                )

            def _kompile_haskell() -> None:
                kompile_haskell(
                    output_dir=output_dir,
                    debug=debug,
                    verbose=verbose,
                    type_inference_mode=type_inference_mode,
                    ignore_warnings=ignore_warnings,
                )

            with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
                futures = [
                    executor.submit(_kompile_maude),
                    executor.submit(_kompile_haskell),
                ]
                [future.result() for future in futures]

            return output_dir

        case KompileTarget.HASKELL:
            base_args_llvm = KompileArgs(
                main_file=main_file,
                main_module=main_module,
                syntax_module=syntax_module,
                include_dirs=include_dirs,
                md_selector=KompileTarget.LLVM.md_selector,
                hook_namespaces=HOOK_NAMESPACES,
                emit_json=emit_json,
                read_only=read_only,
            )
            kompile_llvm = LLVMKompile(
                base_args=base_args_llvm, ccopts=ccopts, opt_level=optimization, llvm_kompile_type=LLVMKompileType.C
            )
            kompile_haskell = HaskellKompile(base_args=base_args, haskell_binary=haskell_binary)

            def _kompile_llvm() -> None:
                kompile_llvm(
                    output_dir=output_dir / 'llvm-library',
                    debug=debug,
                    verbose=verbose,
                    type_inference_mode=type_inference_mode,
                    ignore_warnings=ignore_warnings,
                )

            def _kompile_haskell() -> None:
                kompile_haskell(
                    output_dir=output_dir,
                    debug=debug,
                    verbose=verbose,
                    type_inference_mode=type_inference_mode,
                    ignore_warnings=ignore_warnings,
                )

            with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
                futures = [
                    executor.submit(_kompile_llvm),
                    executor.submit(_kompile_haskell),
                ]
                [future.result() for future in futures]

            return output_dir

        case _:
            raise ValueError(f'Unsupported target: {target.value}')


def lib_ccopts(plugin_dir: Path, debug_build: bool = False) -> list[str]:
    ccopts = ['-std=c++20']

    if debug_build:
        ccopts += ['-g']

    ccopts += ['-lssl', '-lcrypto', '-lsecp256k1']

    ccopts += [str(plugin_dir / 'krypto.a')]

    if config.NIX_LIBS:
        ccopts += config.NIX_LIBS.split(' ')

    return ccopts


def _warning_ccopts() -> list[str]:
    return ['-Wno-deprecated-declarations']
