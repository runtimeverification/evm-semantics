from __future__ import annotations

from typing import TYPE_CHECKING

from pyk.cli.pyk import parse_toml_args

from kevm_pyk.cli import _create_argument_parser, get_argument_type_setter, get_option_string_destination

from .utils import TEST_DATA_DIR

if TYPE_CHECKING:
    from typing import Final

TEST_TOML: Final = TEST_DATA_DIR / 'kevm_pyk_toml_test.toml'


def test_continue_when_default_toml_absent() -> None:
    parser = _create_argument_parser()
    cmd_args = ['run', str(TEST_TOML)]
    args = parser.parse_args(cmd_args)
    assert hasattr(args, 'config_file')
    assert str(args.config_file) == 'kevm-pyk.toml'
    assert hasattr(args, 'config_profile')
    assert str(args.config_profile) == 'default'
    args_dict = parse_toml_args(args)
    assert len(args_dict) == 0


def test_toml_arg_types() -> None:
    parser = _create_argument_parser()
    cmd_args = ['show-kcfg', '--config-file', str(TEST_TOML), str(TEST_TOML)]
    args = parser.parse_args(cmd_args)
    args_dict = parse_toml_args(args, get_option_string_destination, get_argument_type_setter)
    assert 'nodes' in args_dict


def test_toml_read() -> None:
    parser = _create_argument_parser()
    cmd_args = ['run', '--config-file', str(TEST_TOML), str(TEST_TOML), '--verbose']
    args = parser.parse_args(cmd_args)
    args_dict = parse_toml_args(args, get_option_string_destination, get_argument_type_setter)
    assert 'usegas' in args_dict
    assert not args_dict['usegas']
    assert hasattr(args, 'verbose')
    assert args.verbose


def test_toml_profiles() -> None:
    parser = _create_argument_parser()
    cmd_args = ['run', '--config-file', str(TEST_TOML), '--config-profile', 'a_profile', str(TEST_TOML)]
    args = parser.parse_args(cmd_args)
    args_dict = parse_toml_args(args, get_option_string_destination, get_argument_type_setter)
    assert 'debugger' in args_dict
    assert args_dict['debugger']
    assert 'usegas' in args_dict
    assert args_dict['usegas']
