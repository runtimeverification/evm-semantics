from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser
from functools import reduce
from itertools import chain
from typing import TYPE_CHECKING

from pyk.cli_utils import file_path
from pyk.kore.prelude import INT, LBL_MAP, LBL_MAP_ITEM, STOP_MAP, STRING, int_dv, string_dv
from pyk.kore.syntax import DV, App, RightAssoc, SortApp, String, SymbolId

if TYPE_CHECKING:
    from argparse import Namespace
    from collections.abc import Iterable
    from pathlib import Path
    from typing import Any, Final

    from pyk.kore.syntax import Pattern, Sort

_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'

SORT_K_CONFIG_VAR: Final = SortApp('SortKConfigVar')
SORT_K_ITEM: Final = SortApp('SortKItem')
SORT_JSON: Final = SortApp('SortJSON')
SORT_JSON_KEY: Final = SortApp('SortJSONKey')

LBL_JSONS: Final = SymbolId('LblJSONs')
LBL_JSON_LIST: Final = SymbolId('LblJSONList')
LBL_JSON_OBJECT: Final = SymbolId('LblJSONObject')
LBL_JSON_ENTRY: Final = SymbolId('LblJSONEntry')
INJ: Final = SymbolId('inj')

STOP_JSONS: Final = App("Lbl'Stop'List'LBraQuot'JSONs'QuotRBraUnds'JSONs")


def gst_to_kore(gst_data: Any, schedule: str, mode: str, chainid: int) -> App:
    entries = (
        _config_map_entry('PGM', _json_to_kore(gst_data), SORT_JSON),
        _config_map_entry('SCHEDULE', _schedule_to_kore(schedule), SortApp('SortSchedule')),
        _config_map_entry('MODE', _mode_to_kore(mode), SortApp('SortMode')),
        _config_map_entry('CHAINID', _chainid_to_kore(chainid), INT),
    )
    return App(
        'LblinitGeneratedTopCell',
        (),
        (reduce(lambda x, y: App(LBL_MAP, (), (x, y)), entries, STOP_MAP),),
    )


def _config_map_entry(var: str, value: Pattern, sort: Sort) -> App:
    return App(
        LBL_MAP_ITEM,
        (),
        (
            _sort_injection(SORT_K_CONFIG_VAR, SORT_K_ITEM, _k_config_var(var)),
            _sort_injection(sort, SORT_K_ITEM, value),
        ),
    )


def _sort_injection(sort1: Sort, sort2: Sort, pattern: Pattern) -> App:
    return App(INJ, (sort1, sort2), (pattern,))


def _k_config_var(_data: str) -> DV:
    return DV(SORT_K_CONFIG_VAR, String(f'${_data}'))


def _json_to_kore(_data: Any, *, sort: Sort | None = None) -> Pattern:
    if sort is None:
        sort = SORT_JSON

    if isinstance(_data, list):
        return App(LBL_JSON_LIST, (), (_jsons(_json_to_kore(elem) for elem in _data),))

    if isinstance(_data, dict):
        return App(
            LBL_JSON_OBJECT,
            (),
            (
                _jsons(
                    App(LBL_JSON_ENTRY, (), (_json_to_kore(key, sort=SORT_JSON_KEY), _json_to_kore(value)))
                    for key, value in _data.items()
                ),
            ),
        )

    if isinstance(_data, str):
        return _sort_injection(STRING, sort, string_dv(_data))

    if isinstance(_data, int):
        return _sort_injection(INT, sort, int_dv(_data))

    raise AssertionError()


def _jsons(patterns: Iterable[Pattern]) -> RightAssoc:
    return RightAssoc(App(LBL_JSONS, (), chain(patterns, [STOP_JSONS])))


def _schedule_to_kore(schedule: str) -> App:
    return App(f"Lbl{schedule}'Unds'EVM")


def _chainid_to_kore(chainid: int) -> DV:
    return int_dv(chainid)


def _mode_to_kore(mode: str) -> App:
    return App(f'Lbl{mode}')


def main() -> None:
    sys.setrecursionlimit(15000000)
    args = _parse_args()
    _exec_gst_to_kore(args.input_file, args.schedule, args.mode, args.chainid)


def _exec_gst_to_kore(input_file: Path, schedule: str, mode: str, chainid: int) -> None:
    gst_data = json.loads(input_file.read_text())
    kore = gst_to_kore(gst_data, schedule, mode, chainid)
    kore.write(sys.stdout)
    sys.stdout.write('\n')
    _LOGGER.info('Finished writing KORE')


def _parse_args() -> Namespace:
    schedules = (
        'DEFAULT',
        'FRONTIER',
        'HOMESTEAD',
        'TANGERINE_WHISTLE',
        'SPURIOUS_DRAGON',
        'BYZANTIUM',
        'CONSTANTINOPLE',
        'PETERSBURG',
        'ISTANBUL',
        'BERLIN',
        'LONDON',
        'MERGE',
    )
    modes = ('NORMAL', 'VMTESTS')

    parser = ArgumentParser(description='Convert a GeneralStateTest to Kore for compsumption by KEVM')
    parser.add_argument('input_file', type=file_path, help='path to GST')
    parser.add_argument(
        '--schedule',
        choices=schedules,
        default='LONDON',
        help=f"schedule to use for execution [{'|'.join(schedules)}]",
    )
    parser.add_argument('--chainid', type=int, default=1, help='chain ID to use for execution')
    parser.add_argument(
        '--mode',
        choices=modes,
        default='NORMAL',
        help="execution mode to use [{'|'.join(modes)}]",
    )
    return parser.parse_args()


if __name__ == '__main__':
    main()
