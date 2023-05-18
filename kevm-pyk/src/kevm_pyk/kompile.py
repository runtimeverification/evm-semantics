from __future__ import annotations

import logging
import sys
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.cli_utils import run_process
from pyk.ktool.kompile import HaskellKompile, KompileArgs, KompileBackend, LLVMKompile

from . import config

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.ktool.kompile import Kompile, LLVMKompileType


_LOGGER: Final = logging.getLogger(__name__)


HOOK_NAMESPACES: Final = ('JSON', 'KRYPTO', 'BLOCKCHAIN')
CONCRETE_RULES: Final = (
    'EVM.allBut64th.pos',
    'EVM.Caddraccess',
    'EVM.Cbalance.new',
    'EVM.Cbalance.old',
    'EVM.Cextcodecopy.new',
    'EVM.Cextcodecopy.old',
    'EVM.Cextcodehash.new',
    'EVM.Cextcodehash.old',
    'EVM.Cextcodesize.new',
    'EVM.Cextcodesize.old',
    'EVM.Cextra.new',
    'EVM.Cextra.old',
    'EVM.Cgascap',
    'EVM.Cmem',
    'EVM.Cmodexp.new',
    'EVM.Cmodexp.old',
    'EVM.Csload.new',
    'EVM.Csstore.new',
    'EVM.Csstore.old',
    'EVM.Cstorageaccess',
    'EVM.ecrec',
    'EVM.#memoryUsageUpdate.some',
    'EVM.Rsstore.new',
    'EVM.Rsstore.old',
    'EVM-TYPES.bytesRange',
    'EVM-TYPES.padRightToWidthNonEmpty',
    'EVM-TYPES.padToWidthNonEmpty',
    'EVM-TYPES.powmod.nonzero',
    'EVM-TYPES.powmod.zero',
    'EVM-TYPES.signextend.invalid',
    'EVM-TYPES.signextend.negative',
    'EVM-TYPES.signextend.positive',
    'EVM-TYPES.upDivInt',
    'SERIALIZATION.addrFromPrivateKey',
    'SERIALIZATION.keccak',
    'SERIALIZATION.#newAddr',
    'SERIALIZATION.#newAddrCreate2',
)


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


def kevm_kompile(
    target: KompileTarget,
    *,
    output_dir: Path | None = None,
    main_file: Path,
    main_module: str | None,
    syntax_module: str | None,
    includes: Iterable[str] = (),
    emit_json: bool,
    read_only: bool = False,
    ccopts: Iterable[str] = (),
    optimization: int = 0,
    llvm_kompile_type: LLVMKompileType | None = None,
    enable_llvm_debug: bool = False,
    debug: bool = False,
) -> Path:
    backend = target.backend
    md_selector = 'k & ! standalone' if target == KompileTarget.NODE else 'k & ! node'

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
    haskell_binary = not (Kernel.get() == Kernel.DARWIN)
    match backend:
        case KompileBackend.LLVM:
            ccopts = list(ccopts) + _lib_ccopts()
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
                concrete_rules=CONCRETE_RULES,
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


def _lib_ccopts() -> list[str]:
    ccopts = ['-g', '-std=c++14', '-lff', '-lcryptopp', '-lsecp256k1', '-lssl', '-lcrypto']

    libff_dir = config.KEVM_LIB / 'libff'
    ccopts += [f'-L{libff_dir}/lib', f'-I{libff_dir}/include']

    plugin_include = config.KEVM_LIB / 'blockchain-k-plugin/include'
    ccopts += [
        f'{plugin_include}/c/plugin_util.cpp',
        f'{plugin_include}/c/crypto.cpp',
        f'{plugin_include}/c/blake2.cpp',
    ]

    kernel = Kernel.get()
    if kernel == Kernel.DARWIN:
        if not config.NIX_BUILD:
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

            libcryptopp_dir = config.KEVM_LIB / 'cryptopp'
            ccopts += [
                f'-I{libcryptopp_dir}/include',
                f'-L{libcryptopp_dir}/lib',
            ]
    elif kernel == Kernel.LINUX:
        ccopts += ['-lprocps']
    else:
        raise AssertionError()

    return ccopts
