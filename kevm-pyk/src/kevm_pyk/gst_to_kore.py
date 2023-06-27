from __future__ import annotations

import json
import logging
import sys
from argparse import ArgumentParser
from typing import TYPE_CHECKING

from pyk.cli.utils import file_path
from pyk.kore.prelude import INT, SORT_JSON, SORT_K_ITEM, inj, int_dv, json_to_kore, top_cell_initializer
from pyk.kore.syntax import App, SortApp

from .cli import KEVMCLIArgs

if TYPE_CHECKING:
    from argparse import Namespace
    from pathlib import Path
    from typing import Any, Final


_LOGGER: Final = logging.getLogger(__name__)
_LOG_FORMAT: Final = '%(levelname)s %(asctime)s %(name)s - %(message)s'


SORT_SCHEDULE: Final = SortApp('SortSchedule')
SORT_MODE: Final = SortApp('SortMode')


def gst_to_kore(gst_data: Any, schedule: str, mode: str, chainid: int) -> App:
    config = {
        '$PGM': inj(SORT_JSON, SORT_K_ITEM, json_to_kore(gst_data)),
        '$SCHEDULE': inj(SORT_SCHEDULE, SORT_K_ITEM, _schedule_to_kore(schedule)),
        '$MODE': inj(SORT_MODE, SORT_K_ITEM, _mode_to_kore(mode)),
        '$CHAINID': inj(INT, SORT_K_ITEM, int_dv(chainid)),
    }
    return top_cell_initializer(config)


def _schedule_to_kore(schedule: str) -> App:
    return App(f"Lbl{schedule}'Unds'EVM")


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
    kevm_cli_args = KEVMCLIArgs()
    parser = ArgumentParser(
        description='Convert a GeneralStateTest to Kore for compsumption by KEVM',
        parents=[kevm_cli_args.evm_chain_args],
    )
    parser.add_argument('input_file', type=file_path, help='path to GST')
    return parser.parse_args()


if __name__ == '__main__':
    main()
