from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from kevm_pyk import config
from kevm_pyk.__main__ import exec_solc_to_k
from kevm_pyk.kompile import KompileTarget, kevm_kompile

if TYPE_CHECKING:
    from typing import Final

    from pytest import CaptureFixture


EXAMPLES_DIR: Final = (Path(__file__).parent / 'test-data/examples').resolve(strict=True)
TEST_DATA: Final = tuple(EXAMPLES_DIR.glob('*.sol'))


@pytest.mark.parametrize(
    'contract_file',
    TEST_DATA,
    ids=[contract_file.name for contract_file in TEST_DATA],
)
def test_solc_to_k(contract_file: Path, tmp_path: Path, capsys: CaptureFixture[str]) -> None:
    # Given
    contract_name = contract_file.stem
    main_module_name = f'{contract_name.upper()}-VERIFICATION'
    main_file = tmp_path / f'{contract_name.lower()}-bin-runtime.k'
    definition_dir = tmp_path / 'kompiled'

    # When
    exec_solc_to_k(  # TODO extract library function from command line entrypoint
        definition_dir=config.HASKELL_DIR,
        contract_file=contract_file,
        contract_name=contract_name,
        main_module=main_module_name,
        requires=[],
        imports=[],
    )

    k_text = capsys.readouterr().out
    main_file.write_text(k_text)

    kevm_kompile(
        target=KompileTarget.HASKELL,
        main_file=main_file,
        output_dir=definition_dir,
        main_module=main_module_name,
        syntax_module=main_module_name,
    )
