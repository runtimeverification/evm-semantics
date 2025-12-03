from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser
from typing import TYPE_CHECKING

from pyk.cli.utils import file_path
from pyk.kore.prelude import (
    BOOL,
    INT,
    SORT_JSON,
    SORT_K_ITEM,
    STRING,
    SymbolId,
    bool_dv,
    inj,
    int_dv,
    json_entry,
    json_key,
    json_to_kore,
    str_dv,
    top_cell_initializer,
    kseq,
)
from pyk.kore.syntax import App, SortApp
from pyk.utils import single

from .cli import KEVMCLIArgs
from pyk.kdist import kdist
from pyk.kore.tools import PrintOutput, kore_print
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
SORT_ETHEREUM_COMMAND: Final = SortApp('SortEthereumCommand')
LBL_LOAD: Final = SymbolId("LblEthereumCommand'Unds'load")
LBL_RUN: Final = SymbolId("LblEthereumCommand'Unds'run")
LBL_PROCESS:Final = SymbolId("LblEthereumCommand'Unds'process")
LBL_CHECK: Final = SymbolId("LblEthereumCommand'Unds'check")
LBL_ETC_ETS: Final = SymbolId('LblEthereumSimulation')
LBL_JSON_ENTRY: Final = SymbolId('LblJSONEntry')

ETS_SUCCESS: Final = App(SymbolId("LblEthereumCommand'Unds'success"))
ETS_DOT: Final = App(SymbolId("LblEthereumSimulation'Unds'dot"))

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
    loads = []
    test_id = single(gst_data.keys())
    test_data = gst_data[test_id]
    runs = {}
    checks = []

    for key, val in test_data.items():
        if key in _GST_DISCARD_KEYS:
            continue
        elif key in _GST_LOAD_KEYS:
            loads.append((key, val))
        elif key in _GST_CHECK_KEYS:
            checks.append((key, val))
        else:
            runs[key] = val

    pgm = build_pgm(loads, runs, test_id, checks)
    return kore_pgm_to_kore(pgm, SORT_ETHEREUM_SIMULATION, schedule, mode, chainid, usegas)


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


def load_cmd(key: str, val: Any) -> App:
    if key == 'network':
        # "network" : "Cancun" as JSON entry,
        kore_val = inj(STRING, SORT_JSON, str_dv(val))
    else:
        # {"env": {..}} nested JSON obj.
        kore_val = json_to_kore(val)

    pair = json_entry(json_key(key), kore_val)
    return App(LBL_LOAD, (), (pair,))

def run_cmd(test_id: str, obj: dict) -> App:
#    Build: TESTID : { obj }
    inner_json = json_to_kore(obj)  # { obj } as JSON object
    entry = json_entry(json_key(test_id), inner_json)  # TESTID : { obj }
    return App(LBL_RUN, (), (entry,))

def process_cmd(test_id: str, obj: dict) -> App:
    json_kore = json_to_kore({test_id: obj})
    return App(LBL_PROCESS, (), (json_kore,))

def check_cmd(key: str, val: Any,test_id: str) -> App:
    if key in _GST_ALL_POST_KEYS:
        inner = json_to_kore({"post": val})
    elif key in _GST_CHECK_KEYS:
        inner = json_to_kore({key: val})
    else:
        raise ValueError
    entry = json_entry(json_key(test_id), inner)
    return App(LBL_CHECK, (), (entry,))

def build_pgm(loads: list[tuple[str, Any]], rest: dict, test_id: str, checks: list[tuple[str, Any]]) -> Pattern:
    load_apps = [load_cmd(k, v) for k, v in loads]
    run_app = run_cmd(test_id, rest)
    check_app = [check_cmd(k, v,test_id) for k, v in checks]
    all_cmds = load_apps + [run_app] + check_app

    # Build EthereumSimulation: cmd1 ~> cmd2 ~> ... ~> success ~> .EthereumSimulation
    result = App(LBL_ETC_ETS, (), (ETS_SUCCESS, ETS_DOT)) # success ~> .EthereumSimulation
    for prod in reversed(all_cmds):
        result = App(LBL_ETC_ETS, (), (prod, result))

    return result

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
