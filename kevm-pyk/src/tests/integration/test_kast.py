from pyk.kdist import kdist
from pyk.ktool.kprint import KAstInput, KAstOutput, _kast

from ..utils import REPO_ROOT


def test_parse(update_expected_output: bool) -> None:
    # Given
    evm_file = REPO_ROOT / 'tests/interactive/sumTo10.evm'
    expected_file = REPO_ROOT / 'tests/interactive/sumTo10.evm.parse-expected'
    expected = expected_file.read_text()

    # When
    actual = _kast(
        file=evm_file,
        definition_dir=kdist.get('evm-semantics.llvm'),
        input=KAstInput.PROGRAM,
        output=KAstOutput.KORE,
    ).stdout

    # Then
    if update_expected_output:
        expected_file.write_text(actual)
        return

    assert actual == expected
