from __future__ import annotations

import logging
import sys
from enum import Enum
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.ktool.kompile import KompileBackend, kompile

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


class KEVMKompileMode(Enum):
    NODE = 'node'
    STANDALONE = 'standalone'


def kevm_kompile(
    definition_dir: Path,
    backend: KompileBackend,
    main_file: Path,
    emit_json: bool = True,
    includes: Iterable[str] = (),
    main_module_name: str | None = None,
    syntax_module_name: str | None = None,
    md_selector: str | None = None,
    debug: bool = False,
    ccopts: Iterable[str] = (),
    llvm_kompile: bool = True,
    optimization: int = 0,
    llvm_kompile_type: LLVMKompileType | None = None,
    enable_llvm_debug: bool = False,
) -> Path:
    try:
        kompile(
            main_file=main_file,
            output_dir=definition_dir,
            backend=backend,
            emit_json=emit_json,
            include_dirs=[include for include in includes if Path(include).exists()],
            main_module=main_module_name,
            syntax_module=syntax_module_name,
            md_selector=md_selector,
            hook_namespaces=HOOK_NAMESPACES,
            debug=debug,
            concrete_rules=CONCRETE_RULES if backend == KompileBackend.HASKELL else (),
            ccopts=ccopts,
            no_llvm_kompile=not llvm_kompile,
            opt_level=optimization or None,
            llvm_kompile_type=llvm_kompile_type,
            enable_llvm_debug=enable_llvm_debug,
        )
    except RuntimeError as err:
        sys.stderr.write(f'\nkompile stdout:\n{err.args[1]}\n')
        sys.stderr.write(f'\nkompile stderr:\n{err.args[2]}\n')
        sys.stderr.write(f'\nkompile returncode:\n{err.args[3]}\n')
        sys.stderr.flush()
        raise

    return definition_dir
