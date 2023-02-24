import json
import logging
from pathlib import Path
from typing import Final, Iterable, List, Optional

from pyk.kast.inner import KInner
from pyk.kast.outer import KDefinition, KFlatModule, KImport, KRequire
from pyk.ktool.kompile import KompileBackend

from .kevm import KEVM, Foundry
from .solc_to_k import Contract, contract_to_main_module

_LOGGER: Final = logging.getLogger(__name__)


def foundry_kompile(
    definition_dir: Path,
    profile: bool,
    foundry_out: Path,
    includes: Iterable[str],
    md_selector: Optional[str],
    regen: bool = False,
    rekompile: bool = False,
    requires: Iterable[str] = (),
    imports: Iterable[str] = (),
    ccopts: Iterable[str] = (),
    llvm_kompile: bool = True,
    debug: bool = False,
) -> None:
    main_module = 'FOUNDRY-MAIN'
    syntax_module = 'FOUNDRY-MAIN'
    foundry_definition_dir = foundry_out / 'kompiled'
    foundry_main_file = foundry_definition_dir / 'foundry.k'
    kompiled_timestamp = foundry_definition_dir / 'timestamp'
    srcmap_dir = foundry_out / 'srcmaps'
    requires = ['foundry.md'] + list(requires)
    imports = ['FOUNDRY'] + list(imports)

    if not foundry_definition_dir.exists():
        foundry_definition_dir.mkdir()
    if not srcmap_dir.exists():
        srcmap_dir.mkdir()

    json_paths = _contract_json_paths(foundry_out)
    contracts = [_contract_from_json(json_path) for json_path in json_paths]

    for c in contracts:
        srcmap_file = srcmap_dir / f'{c.name}.json'
        with open(srcmap_file, 'w') as smf:
            smf.write(json.dumps(c.srcmap))
            _LOGGER.info(f'Wrote source map: {srcmap_file}')

    foundry = Foundry(definition_dir, profile=profile)
    empty_config = foundry.definition.empty_config(Foundry.Sorts.FOUNDRY_CELL)

    if regen or not foundry_main_file.exists():
        bin_runtime_definition = _foundry_to_bin_runtime(
            empty_config=empty_config,
            contracts=contracts,
            main_module=main_module,
            requires=requires,
            imports=imports,
        )
        with open(foundry_main_file, 'w') as fmf:
            _LOGGER.info(f'Writing file: {foundry_main_file}')
            _foundry = Foundry(
                definition_dir=definition_dir,
                extra_unparsing_modules=bin_runtime_definition.modules,
            )
            fmf.write(_foundry.pretty_print(bin_runtime_definition) + '\n')

    if regen or rekompile or not kompiled_timestamp.exists():
        _LOGGER.info(f'Kompiling definition: {foundry_main_file}')
        KEVM.kompile(
            foundry_definition_dir,
            KompileBackend.HASKELL,
            foundry_main_file,
            emit_json=True,
            includes=includes,
            main_module_name=main_module,
            syntax_module_name=syntax_module,
            md_selector=md_selector,
            profile=profile,
            debug=debug,
            ccopts=ccopts,
            llvm_kompile=llvm_kompile,
        )


def _contract_json_paths(foundry_out: Path) -> List[str]:
    pattern = '*.sol/*.json'
    paths = foundry_out.glob(pattern)
    json_paths = [str(path) for path in paths]
    json_paths = [json_path for json_path in json_paths if not json_path.endswith('.metadata.json')]
    json_paths = sorted(json_paths)  # Must sort to get consistent output order on different platforms
    return json_paths


def _contract_from_json(json_path: str) -> Contract:
    _LOGGER.info(f'Processing contract file: {json_path}')
    with open(json_path, 'r') as json_file:
        contract_json = json.loads(json_file.read())
    contract_name = json_path.split('/')[-1]
    contract_name = contract_name[0:-5] if contract_name.endswith('.json') else contract_name
    return Contract(contract_name, contract_json, foundry=True)


def _foundry_to_bin_runtime(
    empty_config: KInner,
    contracts: Iterable[Contract],
    main_module: Optional[str],
    requires: Iterable[str],
    imports: Iterable[str],
) -> KDefinition:
    modules = []
    for contract in contracts:
        module = contract_to_main_module(contract, empty_config, imports=imports)
        _LOGGER.info(f'Produced contract module: {module.name}')
        modules.append(module)
    _main_module = KFlatModule(
        main_module if main_module else 'MAIN',
        imports=(KImport(mname) for mname in [_m.name for _m in modules] + list(imports)),
    )
    modules.append(_main_module)

    bin_runtime_definition = KDefinition(
        _main_module.name,
        modules,
        requires=(KRequire(req) for req in list(requires)),
    )

    return bin_runtime_definition
