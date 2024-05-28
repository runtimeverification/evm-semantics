from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser
from functools import reduce
from typing import TYPE_CHECKING

from pyk.cli.utils import file_path
from pyk.kore.prelude import (
    BOOL,
    DOTK,
    INT,
    SORT_K_ITEM,
    bool_dv,
    inj,
    int_dv,
    json_to_kore,
    top_cell_initializer,
)
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
SORT_ETHEREUM_COMMAND: Final = SortApp('SortEthereumCommand')


GST_PRE_KEYS: Final = {'env', 'pre', 'rlp', 'network', 'genesisRLP', 'withdrawals'}
GST_EXEC_KEYS: Final = {'exec', 'lastblockhash'}
GST_POST_KEYS: Final = {'post', 'postState', 'postStateHash'}
GST_CHECK_KEYS: Final = {'expect', 'export', 'expet', 'logs', 'out', 'gas', 'blockHeader', 'transactions', 'uncleHeaders', 'genesisBlockHeader'}
GST_IGNORE_KEYS: Final = {'//', '_info', 'callcreates', 'sealEngine', 'transactionSequence', 'chainname', 'blocks'}


def gst_to_kore(test_name: str, gst_data: Any, schedule: str, mode: str, chainid: int, usegas: bool) -> App:
    for key in gst_data:
        if key not in list(GST_PRE_KEYS) + list(GST_POST_KEYS) + list(GST_EXEC_KEYS) + list(GST_CHECK_KEYS) + list(
            GST_IGNORE_KEYS
        ):
            raise ValueError(f'Unknown testing key: {key}')
    k_cell_sequence = []
    for pre_key in GST_PRE_KEYS:
        if pre_key in gst_data:
            k_cell_sequence.append(App("Lblstate'Unds'utils'Unds'load", [], [json_to_kore({pre_key: gst_data[pre_key]})]))
    if 'exec' in gst_data:
        k_cell_sequence.append(App('LblloadCallState', [], [json_to_kore(gst_data['exec'])]))
    if 'lastblockhash' in gst_data:
        k_cell_sequence.extend(
            [
                App("Lbldriver'Unds'start"),
                App("Lbldriver'Unds'flush"),
                App("Lblevm'Unds'startBlock"),
                App("Lbldriver'Unds'startTx"),
            ]
        )
    for post_key in list(GST_POST_KEYS) + list(GST_CHECK_KEYS):
        if post_key in gst_data:
            actual_post_key = 'post' if post_key in GST_POST_KEYS else post_key
            k_cell_sequence.append(App("Lbldriver'Unds'check", [], [json_to_kore({test_name: {actual_post_key: gst_data[post_key]}})]))
    k_cell_sequence.append(App("Lbldriver'Unds'success"))
    k_cell_sequence.reverse()
    k_cell = DOTK
    for k_cell_item in k_cell_sequence:
        k_cell = App('kseq', (), (k_cell_item, k_cell))
    return kore_pgm_to_kore(k_cell, SORT_ETHEREUM_COMMAND, schedule, mode, chainid, usegas)


def kore_pgm_to_kore(pgm: Pattern, pattern_sort: SortApp, schedule: str, mode: str, chainid: int, usegas: bool) -> App:
    config = {
        '$PGM': pgm,
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
    kore = gst_to_kore('dummy', gst_data, schedule, mode, chainid, usegas)
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
