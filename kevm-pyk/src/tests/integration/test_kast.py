from pyk.ktool.kprint import KAstInput, KAstOutput, _kast

from kevm_pyk.dist import DistTarget

from ..utils import REPO_ROOT


def test_parse() -> None:
    # Given
    evm_file = REPO_ROOT / 'tests/interactive/sumTo10.evm'
    expected_file = REPO_ROOT / 'tests/interactive/sumTo10.evm.parse-expected'
    expected = expected_file.read_text()

    # When
    actual = _kast(
        file=evm_file,
        definition_dir=DistTarget.LLVM.check(),
        input=KAstInput.PROGRAM,
        output=KAstOutput.KORE,
    ).stdout

    # Then
    assert actual == expected
