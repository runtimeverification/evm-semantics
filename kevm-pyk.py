#!/usr/bin/env python3

import argparse
import sys

from pyk       import *
from pyk.ktool import KPrint

sys.setrecursionlimit(15000000)

### KEVM instantiation of pyk

stringToken   = lambda s: KToken('"' + s + '"', 'String')
parseHexBytes = lambda s: KApply('#parseHexBytes(_)_SERIALIZATION_ByteArray_String', [s])

def kevmSymbolTable(symbolTable):
    symbolTable['_orBool_']                                                  = paren(symbolTable['_orBool_'])
    symbolTable['_andBool_']                                                 = paren(symbolTable['_andBool_'])
    symbolTable['notBool_']                                                  = paren(symbolTable['notBool_'])
    symbolTable['_/Int_']                                                    = paren(symbolTable['_/Int_'])
    symbolTable['#Or']                                                       = paren(symbolTable['#Or'])
    symbolTable['#And']                                                      = paren(symbolTable['#And'])
    symbolTable['_Set_']                                                     = paren(symbolTable['_Set_'])
    symbolTable['_|->_']                                                     = paren(symbolTable['_|->_'])
    symbolTable['_Map_']                                                     = paren(lambda m1, m2: m1 + '\n' + m2)
    symbolTable['_AccountCellMap_']                                          = paren(lambda a1, a2: a1 + '\n' + a2)
    symbolTable['AccountCellMapItem']                                        = lambda k, v: v
    symbolTable['_[_:=_]_EVM-TYPES_Memory_Memory_Int_ByteArray']             = lambda m, k, v: m + ' [ '  + k + ' := (' + v + '):ByteArray ]'
    symbolTable['_[_.._]_EVM-TYPES_ByteArray_ByteArray_Int_Int']             = lambda m, s, w: '(' + m + ' [ ' + s + ' .. ' + w + ' ]):ByteArray'
    symbolTable['_<Word__EVM-TYPES_Int_Int_Int']                             = paren(lambda a1, a2: '(' + a1 + ') <Word ('  + a2 + ')' )
    symbolTable['_>Word__EVM-TYPES_Int_Int_Int']                             = paren(lambda a1, a2: '(' + a1 + ') >Word ('  + a2 + ')' )
    symbolTable['_<=Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') <=Word (' + a2 + ')' )
    symbolTable['_>=Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') >=Word (' + a2 + ')' )
    symbolTable['_==Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') ==Word (' + a2 + ')' )
    symbolTable['_s<Word__EVM-TYPES_Int_Int_Int']                            = paren(lambda a1, a2: '(' + a1 + ') s<Word (' + a2 + ')' )
    symbolTable['EVMC_UNDEFINED_INSTRUCTION_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_UNDEFINED_INSTRUCTION'
    symbolTable['EVMC_SUCCESS_NETWORK_EndStatusCode']                        = lambda: 'EVMC_SUCCESS'
    symbolTable['EVMC_STATIC_MODE_VIOLATION_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_STATIC_MODE_VIOLATION'
    symbolTable['EVMC_STACK_UNDERFLOW_NETWORK_ExceptionalStatusCode']        = lambda: 'EVMC_STACK_UNDERFLOW'
    symbolTable['EVMC_STACK_OVERFLOW_NETWORK_ExceptionalStatusCode']         = lambda: 'EVMC_STACK_OVERFLOW'
    symbolTable['EVMC_REVERT_NETWORK_EndStatusCode']                         = lambda: 'EVMC_REVERT'
    symbolTable['EVMC_REJECTED_NETWORK_StatusCode']                          = lambda: 'EVMC_REJECTED'
    symbolTable['EVMC_PRECOMPILE_FAILURE_NETWORK_ExceptionalStatusCode']     = lambda: 'EVMC_PRECOMPILE_FAILURE'
    symbolTable['EVMC_OUT_OF_GAS_NETWORK_ExceptionalStatusCode']             = lambda: 'EVMC_OUT_OF_GAS'
    symbolTable['EVMC_INVALID_MEMORY_ACCESS_NETWORK_ExceptionalStatusCode']  = lambda: 'EVMC_INVALID_MEMORY_ACCESS'
    symbolTable['EVMC_INVALID_INSTRUCTION_NETWORK_ExceptionalStatusCode']    = lambda: 'EVMC_INVALID_INSTRUCTION'
    symbolTable['EVMC_INTERNAL_ERROR_NETWORK_StatusCode']                    = lambda: 'EVMC_INTERNAL_ERROR'
    symbolTable['EVMC_FAILURE_NETWORK_ExceptionalStatusCode']                = lambda: 'EVMC_FAILURE'
    symbolTable['EVMC_CALL_DEPTH_EXCEEDED_NETWORK_ExceptionalStatusCode']    = lambda: 'EVMC_CALL_DEPTH_EXCEEDED'
    symbolTable['EVMC_BALANCE_UNDERFLOW_NETWORK_ExceptionalStatusCode']      = lambda: 'EVMC_BALANCE_UNDERFLOW'
    symbolTable['EVMC_BAD_JUMP_DESTINATION_NETWORK_ExceptionalStatusCode']   = lambda: 'EVMC_BAD_JUMP_DESTINATION'
    symbolTable['EVMC_ACCOUNT_ALREADY_EXISTS_NETWORK_ExceptionalStatusCode'] = lambda: 'EVMC_ACCOUNT_ALREADY_EXISTS'
    return symbolTable

### Main

kevmPykArgs = argparse.ArgumentParser()

kevmPykCommandParsers = kevmPykArgs.add_subparsers(dest = 'command')

kevmSolcArgs = kevmPykCommandParsers.add_parser('solc-to-k', help = 'Output helper K definition for given JSON output from solc compiler.')
kevmSolcArgs.add_argument('directoryx',  type = str, help = 'Path to *-kompiled directory to use.')
kevmSolcArgs.add_argument('sol', type = str, help = 'Combined JSON output from solc compiler.')
kevmSolcArgs.add_argument('solc-output', type = argparse.FileType('r'), default = '-', help = 'Combined JSON output from solc compiler.')
kevmSolcArgs.add_argument('contract-name', type = str, help = 'Name of contract to generate K helpers for.')

def main(commandLineArgs):
    args = vars(commandLineArgs.parse_args())

    if args['command'] == 'solc-to-k':
        kompiledDirectory = args['directoryx']
        kevm              = KPrint(kompiledDirectory)
        kevm.symbolTable  = kevmSymbolTable(kevm.symbolTable)

        contractFile    = args['sol']
        contractName    = args['contract-name']
        contractJson    = json.loads(args['solc-output'].read())['contracts'][contractFile + ':' + contractName]
        contractAbi     = contractJson['abi']
        contractBin     = '0x' + contractJson['bin-runtime']
        contractStorage = contractJson['storage-layout']

        binRuntimeProduction = KProduction([KTerminal('#binRuntime'), KTerminal('('), KNonTerminal(KSort('Contract')), KTerminal(')')], KSort('ByteArray'), att = KAtt({'klabel': 'binRuntime', 'macro': ''}))

        contractProduction = KProduction([KTerminal(contractName)], KSort('Contract'), att = KAtt({'klabel': contractName}))
        contractMacro      = KRule(KRewrite(KApply('binRuntime', [KConstant(contractName)]), parseHexBytes(stringToken(contractBin))))

        binRuntimeModuleName = contractName.upper() + '-BIN-RUNTIME'
        binRuntimeModule     = KFlatModule(binRuntimeModuleName, ['EDSL'], [binRuntimeProduction, contractProduction, contractMacro])
        binRuntimeDefinition = KDefinition(binRuntimeModuleName, [binRuntimeModule], requires = [KRequire('edsl.md')])

        kevm.symbolTable['binRuntime'] = lambda s: '#binRuntime(' + s + ')'
        kevm.symbolTable[contractName] = lambda: contractName

        sys.stdout.write(kevm.prettyPrint(binRuntimeDefinition) + '\n')
        sys.stdout.flush()

if __name__ == '__main__':
    main(kevmPykArgs)
