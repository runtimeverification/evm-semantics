import logging
from functools import reduce
from typing import Any, Final, Optional

from pyk.kore.prelude import INT, LBL_MAP, LBL_MAP_ITEM, STOP_MAP, STRING, int_dv, string_dv
from pyk.kore.syntax import DV, App, Pattern, Sort, SortApp, String, SymbolId

_LOGGER: Final = logging.getLogger(__name__)

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


def _json_to_kore(_data: Any, *, sort: Optional[Sort] = None) -> Pattern:
    if sort is None:
        sort = SORT_JSON

    if isinstance(_data, list):
        return App(
            LBL_JSON_LIST,
            (),
            (
                reduce(
                    lambda x, y: App(LBL_JSONS, (), (y, x)),
                    reversed([_json_to_kore(elem) for elem in _data]),
                    STOP_JSONS,
                ),
            ),
        )

    if isinstance(_data, dict):
        return App(
            LBL_JSON_OBJECT,
            (),
            (
                reduce(
                    lambda x, y: App(LBL_JSONS, (), (App(LBL_JSON_ENTRY, (), (y[0], y[1])), x)),
                    reversed(
                        [(_json_to_kore(key, sort=SORT_JSON_KEY), _json_to_kore(value)) for key, value in _data.items()]
                    ),
                    STOP_JSONS,
                ),
            ),
        )

    if isinstance(_data, str):
        return _sort_injection(STRING, sort, string_dv(_data))

    if isinstance(_data, int):
        return _sort_injection(INT, sort, int_dv(_data))

    raise AssertionError()


def _schedule_to_kore(schedule: str) -> App:
    return App(f"Lbl{schedule}'Unds'EVM")


def _chainid_to_kore(chainid: int) -> DV:
    return int_dv(chainid)


def _mode_to_kore(mode: str) -> App:
    return App(f'Lbl{mode}')
