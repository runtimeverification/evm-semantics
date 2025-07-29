from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser
from typing import TYPE_CHECKING

from pyk.cli.utils import file_path
from pyk.kore.prelude import BOOL, INT, SORT_JSON, SORT_K_ITEM, bool_dv, inj, int_dv, json_to_kore, top_cell_initializer
from pyk.kore.syntax import App, SortApp

from .cli import KEVMCLIArgs

if TYPE_CHECKING:
    from argparse import Namespace
    from pathlib import Path
    from typing import Any, Final

    from pyk.kore.syntax import Pattern


_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


SORT_SCHEDULE: Final = SortApp('SortSchedule')
SORT_MODE: Final = SortApp('SortMode')
SORT_ETHEREUM_SIMULATION: Final = SortApp('SortEthereumSimulation')

_GST_DISCARD_KEYS: Final = frozenset(
    [
        '//',
        '_info',
        'callcreates',
        'sealEngine',
        'transactionSequence',
        'chainname',
        'lastblockhash',
        'hasBigInt',
        'config',
    ]
)
_GST_LOAD_KEYS: Final = frozenset(
    [
        'env',
        'pre',
        'rlp',
        'network',
        'genesisRLP',
    ]
)
_GST_EXEC_KEYS: Final = frozenset(
    [
        'exec',
        'blocks',
    ]
)
_GST_POST_KEYS: Final = frozenset(
    [
        'post',
        'postState',
        'postStateHash',
    ]
)
_GST_ALL_POST_KEYS: Final = _GST_POST_KEYS.union(['expect', 'export'])
_GST_CHECK_KEYS: Final = _GST_ALL_POST_KEYS.union(
    [
        'logs',
        'out',
        'gas',
        'blockHeader',
        'transactions',
        'uncleHeaders',
        'genesisBlockHeader',
        'withdrawals',
        'blocknumber',
    ]
)


def filter_gst_keys(gst_data: dict) -> dict:
    """
    Filters the discarded keys out of a single GeneralStateTest,
    recursively removing them from nested dicts/lists as well.
    """

    def _remove_discard_keys(obj: Any) -> Any:
        if type(obj) is dict:
            return {k: _remove_discard_keys(v) for k, v in obj.items() if k not in _GST_DISCARD_KEYS}
        elif type(obj) is list:
            return [_remove_discard_keys(item) for item in obj]
        else:
            # If it's neither dict nor list, just return as-is
            return obj

    return _remove_discard_keys(gst_data)


def gst_to_kore(gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool) -> App:
    return kore_pgm_to_kore(json_to_kore(gst_data), SORT_JSON, schedule, mode, chainid, usegas)


def kore_pgm_to_kore(pgm: Pattern, pattern_sort: SortApp, schedule: str, mode: str, chainid: int, usegas: bool) -> App:
    config = {
        '$PGM': inj(pattern_sort, SORT_K_ITEM, pgm),
        '$SCHEDULE': inj(SORT_SCHEDULE, SORT_K_ITEM, _schedule_to_kore(schedule)),
        '$MODE': inj(SORT_MODE, SORT_K_ITEM, _mode_to_kore(mode)),
        '$CHAINID': inj(INT, SORT_K_ITEM, int_dv(chainid)),
        '$USEGAS': inj(BOOL, SORT_K_ITEM, bool_dv(usegas)),
    }
    return top_cell_initializer(config)


def _schedule_to_kore(schedule: str) -> App:
    return App(f"Lbl{schedule}'Unds'EVM")


def _mode_to_kore(mode: str) -> App:
    return App(f'Lbl{mode}')


def main() -> None:
    sys.setrecursionlimit(15000000)
    args = _parse_args()
    _exec_gst_to_kore(args.input_file, args.schedule, args.mode, args.chainid, args.usegas)


def _exec_gst_to_kore(input_file: Path, schedule: str, mode: str, chainid: int, usegas: bool) -> None:
    gst_data = json.loads(input_file.read_text())
    kore = gst_to_kore(gst_data, schedule, mode, chainid, usegas)
    kore.write(sys.stdout)
    sys.stdout.write('\n')
    _LOGGER.info('Finished writing KORE')


def _parse_args() -> Namespace:
    kevm_cli_args = KEVMCLIArgs()
    parser = ArgumentParser(
        description='Convert a GeneralStateTest to Kore for compsumption by KEVM',
        parents=[kevm_cli_args.evm_chain_args],
    )
    parser.add_argument('input_file', type=file_path, help='path to GST')
    return parser.parse_args()


if __name__ == '__main__':
    main()
