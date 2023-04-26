from __future__ import annotations

import logging
import sys
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.cli_utils import run_process
from pyk.ktool.kompile import KompileBackend, kompile

from . import config

if TYPE_CHECKING:
    from collections.abc import Iterable
    from typing import Final

    from pyk.ktool.kompile import LLVMKompileType


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


class KompileTarget(Enum):
    LLVM = 'llvm'
    HASKELL = 'haskell'
    NODE = 'node'
    FOUNDRY = 'foundry'

    @property
    def backend(self) -> KompileBackend:
        match self:
            case self.LLVM | self.NODE:
                return KompileBackend.LLVM
            case self.HASKELL | self.FOUNDRY:
                return KompileBackend.HASKELL
            case _:
                raise AssertionError()


def kevm_kompile(
    definition_dir: Path,
    target: KompileTarget,
    *,
    main_file: Path,
    kevm_lib: Path | None = None,
    main_module: str | None,
    syntax_module: str | None,
    includes: Iterable[str] = (),
    emit_json: bool,
    ccopts: Iterable[str] = (),
    optimization: int = 0,
    llvm_kompile_type: LLVMKompileType | None = None,
    enable_llvm_debug: bool = False,
    debug: bool = False,
) -> Path:
    backend = target.backend
    no_llvm_kompile = target == KompileTarget.NODE
    md_selector = 'k & ! standalone' if target == KompileTarget.NODE else 'k & ! node'

    if backend == KompileBackend.LLVM:
        if kevm_lib is None:
            raise ValueError(f'Parameter kevm_lib must not be None for target: {target.value}')
        ccopts = list(ccopts) + _lib_ccopts(kevm_lib)

    try:
        kompile(
            main_file=main_file,
            output_dir=definition_dir,
            backend=backend,
            emit_json=emit_json,
            include_dirs=[include for include in includes if Path(include).exists()],
            main_module=main_module,
            syntax_module=syntax_module,
            md_selector=md_selector,
            hook_namespaces=HOOK_NAMESPACES,
            concrete_rules=CONCRETE_RULES if backend == KompileBackend.HASKELL else (),
            ccopts=ccopts,
            no_llvm_kompile=no_llvm_kompile,
            opt_level=optimization or None,
            llvm_kompile_type=llvm_kompile_type,
            enable_llvm_debug=enable_llvm_debug,
            debug=debug,
        )
    except RuntimeError as err:
        sys.stderr.write(f'\nkompile stdout:\n{err.args[1]}\n')
        sys.stderr.write(f'\nkompile stderr:\n{err.args[2]}\n')
        sys.stderr.write(f'\nkompile returncode:\n{err.args[3]}\n')
        sys.stderr.flush()
        raise

    return definition_dir


def _lib_ccopts(kevm_lib: Path) -> list[str]:
    ccopts = ['-g', '-std=c++14', '-lff', '-lcryptopp', '-lsecp256k1', '-lssl', '-lcrypto']

    libff_dir = kevm_lib / 'libff'
    ccopts += [f'-L{libff_dir}/lib', f'-I{libff_dir}/include']

    plugin_include = kevm_lib / 'blockchain-k-plugin/include'
    ccopts += [
        f'{plugin_include}/c/plugin_util.cpp',
        f'{plugin_include}/c/crypto.cpp',
        f'{plugin_include}/c/blake2.cpp',
    ]

    class Kernel(Enum):
        LINUX = 'Linux'
        DARWIN = 'Darwin'

        @staticmethod
        def get() -> Kernel:
            uname = run_process(('uname', '-s'), pipe_stderr=True, logger=_LOGGER).stdout.strip()
            return Kernel(uname)

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

            libcryptopp_dir = kevm_lib / 'cryptopp'
            ccopts += [
                f'-I{libcryptopp_dir}/include',
                f'-L{libcryptopp_dir}/lib',
            ]
    elif kernel == Kernel.LINUX:
        ccopts += ['-lprocps']
    else:
        raise AssertionError()

    return ccopts
