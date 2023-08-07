from __future__ import annotations

import logging
import sys
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.ktool.kompile import HaskellKompile, KompileArgs, KompileBackend, LLVMKompile
from pyk.utils import run_process

from . import config

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.ktool.kompile import Kompile, LLVMKompileType


_LOGGER: Final = logging.getLogger(__name__)


HOOK_NAMESPACES: Final = ('JSON', 'KRYPTO', 'BLOCKCHAIN')


class Kernel(Enum):
    LINUX = 'Linux'
    DARWIN = 'Darwin'

    @staticmethod
    def get() -> Kernel:
        uname = run_process(('uname', '-s'), pipe_stderr=True, logger=_LOGGER).stdout.strip()
        return Kernel(uname)


class KompileTarget(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    HASKELL_STANDALONE = 'haskell-standalone'
    NODE = 'node'
    FOUNDRY = 'foundry'

    @property
    def backend(self) -> KompileBackend:
        match self:
            case self.LLVM | self.NODE:
                return KompileBackend.LLVM
            case self.HASKELL | self.FOUNDRY | self.HASKELL_STANDALONE:
                return KompileBackend.HASKELL
            case _:
                raise AssertionError()

    @property
    def definition_dir(self) -> Path:
        match self:
            case self.LLVM:
                return config.LLVM_DIR
            case self.NODE:
                return config.NODE_DIR
            case self.HASKELL:
                return config.HASKELL_DIR
            case self.HASKELL_STANDALONE:
                return config.HASKELL_STANDALONE_DIR
            case self.FOUNDRY:
                return config.FOUNDRY_DIR
            case _:
                raise AssertionError()

    @property
    def md_selector(self) -> str:
        match self:
            case self.LLVM:
                return 'k & ! node & ! symbolic'
            case self.NODE:
                return 'k & ! symbolic & ! standalone'
            case self.HASKELL:
                return 'k & ! node & ! concrete'
            case self.HASKELL_STANDALONE:
                return 'k & ! node & ! concrete'
            case self.FOUNDRY:
                return 'k & ! node & ! concrete'
            case _:
                raise AssertionError()


def kevm_kompile(
    target: KompileTarget,
    *,
    output_dir: Path | None = None,
    main_file: Path,
    main_module: str | None,
    syntax_module: str | None,
    includes: Iterable[str] = (),
    emit_json: bool = True,
    read_only: bool = False,
    ccopts: Iterable[str] = (),
    optimization: int = 0,
    llvm_kompile_type: LLVMKompileType | None = None,
    enable_llvm_debug: bool = False,
    debug: bool = False,
) -> Path:
    backend = target.backend
    md_selector = target.md_selector

    include_dirs = [Path(include) for include in includes]
    include_dirs += [config.INCLUDE_DIR]

    base_args = KompileArgs(
        main_file=main_file,
        main_module=main_module,
        syntax_module=syntax_module,
        include_dirs=include_dirs,
        md_selector=md_selector,
        hook_namespaces=HOOK_NAMESPACES,
        emit_json=emit_json,
        read_only=read_only,
    )

    kompile: Kompile
    kernel = Kernel.get()
    haskell_binary = kernel is not Kernel.DARWIN
    match backend:
        case KompileBackend.LLVM:
            ccopts = list(ccopts) + _lib_ccopts(kernel)
            no_llvm_kompile = target == KompileTarget.NODE
            kompile = LLVMKompile(
                base_args=base_args,
                ccopts=ccopts,
                no_llvm_kompile=no_llvm_kompile,
                opt_level=optimization,
                llvm_kompile_type=llvm_kompile_type,
                enable_llvm_debug=enable_llvm_debug,
            )
        case KompileBackend.HASKELL:
            kompile = HaskellKompile(
                base_args=base_args,
                haskell_binary=haskell_binary,
            )
        case _:
            raise ValueError(f'Unsupported backend: {backend.value}')

    try:
        return kompile(output_dir=output_dir or target.definition_dir, debug=debug)
    except RuntimeError as err:
        sys.stderr.write(f'\nkompile stdout:\n{err.args[1]}\n')
        sys.stderr.write(f'\nkompile stderr:\n{err.args[2]}\n')
        sys.stderr.write(f'\nkompile returncode:\n{err.args[3]}\n')
        sys.stderr.flush()
        raise


def _lib_ccopts(kernel: Kernel) -> list[str]:
    ccopts = ['-g', '-std=c++17']

    ccopts += ['-lssl', '-lcrypto']

    libff_dir = config.KEVM_LIB / 'libff'
    ccopts += [f'{libff_dir}/lib/libff.a', f'-I{libff_dir}/include']

    libcryptopp_dir = config.KEVM_LIB / 'libcryptopp'
    ccopts += [f'{libcryptopp_dir}/lib/libcryptopp.a', f'-I{libcryptopp_dir}/include']

    libsecp256k1_dir = config.KEVM_LIB / 'libsecp256k1'
    ccopts += [f'{libsecp256k1_dir}/lib/libsecp256k1.a', f'-I{libsecp256k1_dir}/include']

    plugin_include = config.KEVM_LIB / 'blockchain-k-plugin/include'
    ccopts += [
        f'{plugin_include}/c/plugin_util.cpp',
        f'{plugin_include}/c/crypto.cpp',
        f'{plugin_include}/c/blake2.cpp',
    ]

    if kernel == Kernel.DARWIN:
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
    elif kernel == Kernel.LINUX:
        ccopts += ['-lprocps']
        if config.NIX_LIBS:
            ccopts += config.NIX_LIBS.split(' ')
    else:
        raise AssertionError()

    return ccopts
