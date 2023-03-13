import json
import logging
from collections import OrderedDict
from functools import reduce
from pathlib import Path
from typing import Any, Final, Optional, TextIO

from pyk.kore.prelude import INT, STRING, int_dv, string_dv
from pyk.kore.syntax import DV, App, Pattern, Sort, SortApp, String

_LOGGER: Final = logging.getLogger(__name__)


def schedule_to_kore(schedule: str) -> App:
    return App(f"Lbl{schedule}'Unds'EVM")


def chainid_to_kore(chainid: int) -> DV:
    return int_dv(chainid)


def mode_to_kore(mode: str) -> App:
    return App(f'Lbl{mode}')


def gst_to_kore(gst_file: Path, out_stream: TextIO, schedule: str, mode: str, chainid: int) -> None:
    with open(gst_file) as data_file:
        data = json.load(data_file, object_pairs_hook=OrderedDict)

    def _k_config_var(_data: str) -> DV:
        return DV(SortApp('SortKConfigVar'), String(f'${_data}'))

    def _sort_injection(sort1: Sort, sort2: Sort, pattern: Pattern) -> App:
        return App('inj', (sort1, sort2), (pattern,))

    def _kast(_data: Any, sort: Optional[Sort] = None) -> Pattern:
        if sort is None:
            sort = SortApp('SortJSON')

        if isinstance(_data, list):
            return App(
                'LblJSONList',
                (),
                (
                    reduce(
                        lambda x, y: App('LblJSONs', (), (y, x)),
                        reversed([_kast(elem) for elem in _data]),
                        App("Lbl'Stop'List'LBraQuot'JSONs'QuotRBraUnds'JSONs"),
                    ),
                ),
            )

        if isinstance(_data, OrderedDict):
            return App(
                'LblJSONObject',
                (),
                (
                    reduce(
                        lambda x, y: App('LblJSONs', (), (App('LblJSONEntry', (), (y[0], y[1])), x)),
                        reversed([(_kast(key, SortApp('SortJSONKey')), _kast(value)) for key, value in _data.items()]),
                        App("Lbl'Stop'List'LBraQuot'JSONs'QuotRBraUnds'JSONs"),
                    ),
                ),
            )

        if isinstance(_data, str):
            return _sort_injection(STRING, sort, string_dv(_data))

        if isinstance(_data, int):
            return _sort_injection(INT, sort, int_dv(_data))

        raise AssertionError()

    def _config_map_entry(var: str, value: Pattern, sort: Sort) -> App:
        return App(
            "Lbl'UndsPipe'-'-GT-Unds'",
            (),
            (
                _sort_injection(SortApp('SortKConfigVar'), SortApp('SortKItem'), _k_config_var(var)),
                _sort_injection(sort, SortApp('SortKItem'), value),
            ),
        )

    entries = (
        _config_map_entry('PGM', _kast(data), SortApp('SortJSON')),
        _config_map_entry('SCHEDULE', schedule_to_kore(schedule), SortApp('SortSchedule')),
        _config_map_entry('MODE', mode_to_kore(mode), SortApp('SortMode')),
        _config_map_entry('CHAINID', chainid_to_kore(chainid), SortApp('SortInt')),
    )
    kore = App(
        'LblinitGeneratedTopCell',
        (),
        (reduce(lambda x, y: App("Lbl'Unds'Map'Unds'", (), (x, y)), entries, App("Lbl'Stop'Map")),),
    )
    out_stream.write(kore.text)
    out_stream.flush()
    _LOGGER.info('Finished writing kore.')
