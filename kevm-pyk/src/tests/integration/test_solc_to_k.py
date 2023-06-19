from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from kevm_pyk.kompile import KompileTarget, kevm_kompile

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from collections.abc import Callable
    from pathlib import Path
    from typing import Final


EXAMPLES_DIR: Final = TEST_DATA_DIR / 'examples'
TEST_DATA: Final = tuple(EXAMPLES_DIR.glob('*.sol'))


@pytest.mark.parametrize(
    'contract_file',
    TEST_DATA,
    ids=[contract_file.name for contract_file in TEST_DATA],
)
def test_solc_to_k(contract_file: Path, bin_runtime: Callable, tmp_path: Path) -> None:
    # Given
    definition_dir = tmp_path / 'kompiled'
    main_file, main_module_name = bin_runtime(contract_file)

    # When
    kevm_kompile(
        target=KompileTarget.HASKELL,
        output_dir=definition_dir,
        main_file=main_file,
        main_module=main_module_name,
        syntax_module=main_module_name,
    )
