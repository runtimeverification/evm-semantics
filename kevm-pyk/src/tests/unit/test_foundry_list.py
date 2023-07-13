from __future__ import annotations

from subprocess import CalledProcessError
from typing import TYPE_CHECKING

from pyk.utils import run_process

from kevm_pyk.foundry import foundry_list
from tests.unit.utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from typing import Final

FORGE_STD_REF: Final = '27e14b7'

LIST_DATA_DIR: Final = TEST_DATA_DIR / 'foundry-list'
LIST_EXPECTED: Final = LIST_DATA_DIR / 'foundry-list.expected'


def test_foundry_list(update_expected_output: bool) -> None:
    with LIST_EXPECTED.open() as f:
        foundry_list_expected = f.read().rstrip()
    assert foundry_list_expected

    try:
        run_process(['forge', 'install', '--no-git', f'foundry-rs/forge-std@{FORGE_STD_REF}'], cwd=LIST_DATA_DIR)
    except CalledProcessError:
        pass

    run_process(['forge', 'build'], cwd=LIST_DATA_DIR)
    list_out = '\n'.join(foundry_list(LIST_DATA_DIR))

    if update_expected_output:
        LIST_EXPECTED.write_text(list_out)
    else:
        assert list_out == foundry_list_expected
