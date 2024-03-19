from __future__ import annotations

import concurrent.futures
import logging
import sys
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.kdist import kdist
from pyk.ktool.kompile import HaskellKompile, KompileArgs, LLVMKompile, LLVMKompileType, MaudeKompile
from pyk.utils import run_process

from . import config

if TYPE_CHECKING:
    from collections.abc import Iterable
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
    includes: Iterable[str] = (),
    emit_json: bool = True,
    read_only: bool = False,
    ccopts: Iterable[str] = (),
    optimization: int = 0,
    llvm_kompile_type: LLVMKompileType | None = None,
    enable_llvm_debug: bool = False,
    llvm_library: Path | None = None,
    plugin_dir: Path | None = None,
    debug_build: bool = False,
    debug: bool = False,
    verbose: bool = False,
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
        llvm_library=llvm_library,
        debug_build=debug_build,
        debug=debug,
        verbose=verbose,
    )


def run_kompile(
    target: KompileTarget,
    output_dir: Path,
    main_file: Path,
    *,
    main_module: str | None,
    syntax_module: str | None,
    includes: Iterable[str] = (),
    emit_json: bool = True,
    read_only: bool = False,
    ccopts: Iterable[str] = (),
    optimization: int = 0,
    llvm_kompile_type: LLVMKompileType | None = None,
    enable_llvm_debug: bool = False,
    llvm_library: Path | None = None,
    debug_build: bool = False,
    debug: bool = False,
    verbose: bool = False,
) -> Path:
    if llvm_library is None:
        llvm_library = output_dir / 'llvm-library'

    include_dirs = [Path(include) for include in includes]
    include_dirs += config.INCLUDE_DIRS

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

    try:
        match target:
            case KompileTarget.LLVM:
                kompile = LLVMKompile(
                    base_args=base_args,
                    ccopts=ccopts,
                    opt_level=optimization,
                    llvm_kompile_type=llvm_kompile_type,
                    enable_llvm_debug=enable_llvm_debug,
                )
                return kompile(output_dir=output_dir, debug=debug, verbose=verbose)

            case KompileTarget.MAUDE:
                kompile_maude = MaudeKompile(
                    base_args=base_args,
                )
                kompile_haskell = HaskellKompile(base_args=base_args)

                maude_dir = output_dir / 'kompiled-maude'

                def _kompile_maude() -> None:
                    kompile_maude(output_dir=maude_dir, debug=debug, verbose=verbose)

                def _kompile_haskell() -> None:
                    kompile_haskell(output_dir=output_dir, debug=debug, verbose=verbose)

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
                    kompile_llvm(output_dir=llvm_library, debug=debug, verbose=verbose)

                def _kompile_haskell() -> None:
                    kompile_haskell(output_dir=output_dir, debug=debug, verbose=verbose)

                with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
                    futures = [
                        executor.submit(_kompile_llvm),
                        executor.submit(_kompile_haskell),
                    ]
                    [future.result() for future in futures]

                return output_dir

            case _:
                raise ValueError(f'Unsupported target: {target.value}')

    except RuntimeError as err:
        sys.stderr.write(f'\nkompile stdout:\n{err.args[1]}\n')
        sys.stderr.write(f'\nkompile stderr:\n{err.args[2]}\n')
        sys.stderr.write(f'\nkompile returncode:\n{err.args[3]}\n')
        sys.stderr.flush()
        raise


def lib_ccopts(plugin_dir: Path, debug_build: bool = False) -> list[str]:
    kernel = sys.platform

    ccopts = ['-std=c++17']

    if debug_build:
        ccopts += ['-g']

    ccopts += ['-lssl', '-lcrypto', '-lsecp256k1']

    libff_dir = plugin_dir / 'libff'
    ccopts += [f'{libff_dir}/lib/libff.a', f'-I{libff_dir}/include']

    libcryptopp_dir = plugin_dir / 'libcryptopp'
    ccopts += [f'{libcryptopp_dir}/lib/libcryptopp.a', f'-I{libcryptopp_dir}/include']

    plugin_include = plugin_dir / 'plugin-c'
    ccopts += [
        f'{plugin_include}/plugin_util.cpp',
        f'{plugin_include}/crypto.cpp',
        f'{plugin_include}/blake2.cpp',
    ]

    if kernel == 'darwin':
        if not config.NIX_LIBS:
            brew_root = run_process(('brew', '--prefix'), pipe_stderr=True, logger=_LOGGER).stdout.strip()
            ccopts += [
                f'-I{brew_root}/include',
                f'-L{brew_root}/lib',
            ]

            openssl_root = run_process(('brew', '--prefix', 'openssl'), pipe_stderr=True, logger=_LOGGER).stdout.strip()
            ccopts += [
                f'-I{openssl_root}/include',
                f'-L{openssl_root}/lib',
            ]
        else:
            ccopts += config.NIX_LIBS.split(' ')
    elif kernel == 'linux':
        ccopts += ['-lprocps']
        if config.NIX_LIBS:
            ccopts += config.NIX_LIBS.split(' ')
    else:
        raise AssertionError()

    return ccopts


def _warning_ccopts() -> list[str]:
    return ['-Wno-deprecated-declarations']
