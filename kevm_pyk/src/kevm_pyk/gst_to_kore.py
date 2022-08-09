import json
import logging
from collections import OrderedDict
from io import TextIOWrapper
from pathlib import Path
from typing import Any, Callable, Final

_LOGGER: Final = logging.getLogger(__name__)


def schedule_to_kore(schedule: str) -> str:
    return f'Lbl{schedule}' + "'Unds'EVM{}()"


def chainid_to_kore(chainid: int) -> str:
    return "\\dv{SortInt{}}(" + f'"{chainid}")'


def mode_to_kore(mode: str) -> str:
    return f'Lbl{mode}' + "{}()"


def gst_to_kore(gst_file: Path, out_stream: TextIOWrapper, schedule: str, mode: str, chainid: int) -> None:

    with open(gst_file) as data_file:
        data = json.load(data_file, object_pairs_hook=OrderedDict)

    def print_int(_data: int) -> None:
        out_stream.write('\\dv{SortInt{}}("')
        out_stream.write(str(_data))
        out_stream.write('")')

    def print_string(_data: str) -> None:
        out_stream.write('\\dv{SortString{}}(')
        out_stream.write(json.dumps(_data))
        out_stream.write(')')

    def print_k_config_var(_data: str) -> None:
        out_stream.write('\\dv{SortKConfigVar{}}("$' + _data + '")')

    def print_sort_injection(s1: str, s2: str, _data: Any, printer: Callable[[Any], None]) -> None:
        out_stream.write('inj{Sort' + s1 + '{}, ' + 'Sort' + s2 + '{}}(')
        printer(_data)
        out_stream.write(')')

    def print_kast(_data: Any, sort='JSON'):
        if isinstance(_data, list):
            out_stream.write('LblJSONList{}(')
            for elem in _data:
                out_stream.write('LblJSONs{}(')
                print_kast(elem)
                out_stream.write(',')
            out_stream.write('Lbl\'Stop\'List\'LBraQuot\'JSONs\'QuotRBraUnds\'JSONs{}()')
            for elem in _data:
                out_stream.write(')')
            out_stream.write(')')
        elif isinstance(_data, OrderedDict):
            out_stream.write('LblJSONObject{}(')
            for key, value in _data.items():
                out_stream.write('LblJSONs{}(LblJSONEntry{}(')
                print_kast(key, sort='JSONKey')
                out_stream.write(',')
                print_kast(value)
                out_stream.write('),')
            out_stream.write('Lbl\'Stop\'List\'LBraQuot\'JSONs\'QuotRBraUnds\'JSONs{}()')
            for key in _data:
                out_stream.write(')')
            out_stream.write(')')
        elif isinstance(_data, str):
            print_sort_injection('String', sort, _data, print_string)
        elif isinstance(_data, int):
            print_sort_injection('Int', sort, _data, print_int)
        else:
            out_stream.write(str(type(_data)))
            raise AssertionError

    def print_direct(s: str) -> None:
        out_stream.write(s)

    def print_config_map_entry(k: str, v: str, vsort: str, vprint: Callable[[Any], None]) -> None:
        out_stream.write('Lbl\'UndsPipe\'-\'-GT-Unds\'{}(')
        print_sort_injection('KConfigVar', 'KItem', k, print_k_config_var)
        out_stream.write(',')
        print_sort_injection(vsort, 'KItem', v, vprint)
        out_stream.write(')')

    out_stream.write('LblinitGeneratedTopCell{}(Lbl\'Unds\'Map\'Unds\'{}(Lbl\'Unds\'Map\'Unds\'{}(Lbl\'Unds\'Map\'Unds\'{}(Lbl\'Unds\'Map\'Unds\'{}(Lbl\'Stop\'Map{}(),')
    print_config_map_entry('PGM', data, 'JSON', print_kast)
    out_stream.write('),')
    print_config_map_entry('SCHEDULE', schedule_to_kore(schedule), 'Schedule', print_direct)
    out_stream.write('),')
    print_config_map_entry('MODE', mode_to_kore(mode), 'Mode', print_direct)
    out_stream.write('),')
    print_config_map_entry('CHAINID', chainid_to_kore(chainid), 'Int', print_direct)
    out_stream.write('))\n')
    out_stream.write('\n')
    out_stream.flush()

    _LOGGER.info('Finished writing kore.')
