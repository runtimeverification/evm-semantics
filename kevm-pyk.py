#!/usr/bin/env python3

import argparse
from datetime import datetime
import os
from pyk import *
from pyk.__main__ import main, pykArgs, pykCommandParsers
from pyk.__init__ import _teeProcessStdout
import sys
import tempfile

sys.setrecursionlimit(15000000)

### UPSTREAMABLE

def removeGeneratedCells(constrainedTerm):
    """Remove <generatedTop> and <generatedCounter> from a configuration.

    -   Input: Constrained term which contains <generatedTop> and <generatedCounter>.
    -   Output: Constrained term with those cells removed.
    """
    rule = ( KApply('<generatedTop>', [ KVariable('CONFIG') , KApply('<generatedCounter>', [KVariable('_')]) ])
           , KVariable('CONFIG')
           )
    return rewriteAnywhereWith(rule, constrainedTerm)

def makeDefinition(sents, specModuleName, mainFileName, mainModuleName):
    module = KFlatModule(specModuleName, [mainModuleName], sents)
    return KDefinition(specModuleName, [module], requires = [KRequire(mainFileName.split('/')[-1])])

def isAnonVariable(kast):
    return isKVariable(kast) and kast['name'].startswith('_')

def getCell(constrainedTerm, cellVariable):
    (state, _) = splitConfigAndConstraints(constrainedTerm)
    (_, subst) = splitConfigFrom(state)
    return subst[cellVariable]

def setCell(constrainedTerm, cellVariable, cellValue):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    (config, subst)     = splitConfigFrom(state)
    subst[cellVariable] = cellValue
    return KApply('#And', [substitute(config, subst), constraint])

def structurallyFrameKCell(constrainedTerm):
    kCell = getCell(constrainedTerm, 'K_CELL')
    if isKSequence(kCell) and len(kCell['items']) > 0 and isAnonVariable(kCell['items'][-1]):
        kCell = KSequence(kCell['items'][0:-1] + [ktokenDots])
    return setCell(constrainedTerm, 'K_CELL', kCell)

def applyCellSubst(constrainedTerm, cellSubst):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    (config, subst)     = splitConfigFrom(state)
    for k in cellSubst:
        subst[k] = cellSubst[k]
    return KApply('#And', [substitute(config, subst), constraint])

def printConstraint(constraint, symbolTable):
    return prettyPrintKast(simplifyBool(unsafeMlPredToBool(constraint)), symbolTable)

def removeUselessConstraints(constrainedTerm):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    stateVars           = collectFreeVars(state)
    constraints         = flattenLabel('#And', constraint)
    newConstraints      = []
    for c in constraints:
        if all([v in stateVars for v in collectFreeVars(c)]):
            newConstraints.append(c)
    return buildAssoc(KConstant('#Top'), '#And', [state] + newConstraints)

def removeConstraintsFor(varNames, constrainedTerm):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    constraints         = flattenLabel('#And', constraint)
    newConstraints      = []
    for c in constraints:
        if not any([v in varNames for v in collectFreeVars(c)]):
            newConstraints.append(c)
    return buildAssoc(KConstant('#Top'), '#And', [state] + newConstraints)

def boolToMlPred(boolVal, isTrue = True):
    return KApply('#Equals', [KToken('true' if isTrue else 'false', 'Bool'), boolVal])

def buildRule(ruleId, initConstrainedTerm, finalConstrainedTerm, claim = False, priority = None, keepVars = None):
    (initConfig,  initConstraint)  = splitConfigAndConstraints(initConstrainedTerm)
    (finalConfig, finalConstraint) = splitConfigAndConstraints(finalConstrainedTerm)
    ruleBody                       = pushDownRewrites(KRewrite(initConfig, finalConfig))
    ruleConstrainedTerm            = buildAssoc(KConstant('#Top'), '#And', [ruleBody, initConstraint, finalConstraint])
    ruleConstrainedTerm            = removeUselessConstraints(ruleConstrainedTerm)
    ruleConstrainedTerm            = markUselessVars(ruleConstrainedTerm)
    (ruleBody, ruleRequires)       = splitConfigAndConstraints(ruleConstrainedTerm)
    ruleRequires                   = simplifyBooleanConstraint(unsafeMlPredToBool(ruleRequires))
    ruleAtt                        = None if priority is None else KAtt(atts = {'priority': str(priority)})
    if not claim:
        rule = KRule (ruleBody, requires = ruleRequires, att = ruleAtt)
    else:
        rule = KClaim(ruleBody, requires = ruleRequires, att = ruleAtt)
    rule = addAttributes(rule, { 'label': ruleId })
    return minimizeRule(rule, keepVars = keepVars)

def onCells(cellHandler, constrainedTerm):
    """Given an effect and a constrained term, return the effect applied to the cells in the term.

    -   Input: Effect that takes as input a cell name and the contents of the cell, and a constrained term.
    -   Output: Constrained term with the effect applied to each cell.
    """
    (config, constraint) = splitConfigAndConstraints(constrainedTerm)
    constraints          = flattenLabel('#And', constraint)
    (emptyConfig, subst) = splitConfigFrom(config)
    for k in subst:
        newCell = cellHandler(k, subst[k])
        if newCell is not None:
            (term, constraint) = newCell
            subst[k] = term
            if not constraint in constraints:
                constraints.append(constraint)
    return buildAssoc(KConstant('#Top'), '#And', [substitute(emptyConfig, subst)] + constraints)

### Utilities

def _notif(msg):
    sys.stderr.write('== ' + sys.argv[0].split('/')[-1] + ' ' + str(datetime.now()) + ': ' + msg + '\n')
    sys.stderr.flush()

def _warning(msg):
    _notif('[WARNING] ' + msg)

def _fatal(msg, exitCode = 1):
    _notif('[FATAL] ' + msg)
    raise('Quitting')

def _genFileTimestamp(comment = '//'):
    return comment + ' This file generated by: ' + sys.argv[0] + '\n' + comment + ' ' + str(datetime.now()) + '\n'

### KEVM Stuff

boolToken             = lambda b:      KToken(str(b).lower(), 'Bool')
intToken              = lambda i:      KToken(str(i), 'Int')
stringToken           = lambda s:      KToken('"' + s + '"', 'String')
ltInt                 = lambda i1, i2: KApply('_<Int_', [i1, i2])
leInt                 = lambda i1, i2: KApply('_<=Int_', [i1, i2])
rangeUInt256          = lambda i:      KApply('#rangeUInt(_,_)_EVM-TYPES_Bool_Int_Int', [intToken(256), i])
rangeAddress          = lambda i:      KApply('#rangeAddress(_)_EVM-TYPES_Bool_Int', [i])
sizeByteArray         = lambda ba:     KApply('#sizeByteArray(_)_EVM-TYPES_Int_ByteArray', [ba])
infGas                = lambda g:      KApply('infGas', [g])
computeValidJumpDests = lambda p:      KApply('#computeValidJumpDests(_)_EVM_Set_ByteArray', [p])
binRuntime            = lambda c:      KApply('#binRuntime', [c])

def kevmAccountCell(id, balance, code, storage, origStorage, nonce):
    return KApply('<account>', [ KApply('<acctID>'      , [id])
                               , KApply('<balance>'     , [balance])
                               , KApply('<code>'        , [code])
                               , KApply('<storage>'     , [storage])
                               , KApply('<origStorage>' , [origStorage])
                               , KApply('<nonce>'       , [nonce])
                               ]
                 )

def kevmSymbolTable(json_definition, opinionated = True):
    symbolTable                                                              = buildSymbolTable(json_definition, opinionated = opinionated)
    symbolTable['_Set_']                                                     = paren(symbolTable['_Set_'])
    symbolTable['_AccountCellMap_']                                          = paren(lambda a1, a2: a1 + '\n' + a2)
    symbolTable['AccountCellMapItem']                                        = lambda k, v: v
    symbolTable['_[_:=_]_EVM-TYPES_Memory_Memory_Int_ByteArray']             = lambda m, k, v: m + ' [ '  + k + ' := (' + v + '):ByteArray ]'
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

def kevmProve(mainFile, specFile, specModule, kevmArgs = [], teeOutput = False, dieOnFail = False):
    backend = 'haskell'
    backendDirectory = '/'.join(mainFile.split('/')[0:-1])
    kevmCommand = [ 'kevm' , 'prove' , specFile
                  , '--backend' , backend , '--backend-dir' , backendDirectory , '-I' , backendDirectory
                  , '--provex' , '--spec-module' , specModule
                  , '--output' , 'json' , '--boundary-cells' , 'k,pc'
                  ]
    kevmCommand += kevmArgs
    _notif(' '.join(kevmCommand))
    (rc, stdout, stderr) = _teeProcessStdout(kevmCommand, tee = teeOutput)
    try:
        finalState = json.loads(stdout)['term']
        if finalState == KConstant('#Top'):
            return finalState
        if dieOnFail:
            _fatal('Unable to prove claim: ' + specFile)
        finalStates = [ structurallyFrameKCell(s) for s in flattenLabel('#Or', finalState) ]
        return buildAssoc(KConstant('#Bottom'), '#Or', finalStates)
    except:
        sys.stderr.write(stdout + '\n')
        sys.stderr.write(stderr + '\n')
        _fatal('Exiting...', exitCode = rc)

def kevmSanitizeConfig(initConstrainedTerm):

    def _parseableVarNames(cellName, term):
        if isAnonVariable(term) and (term['name'][1:].isdigit() or term['name'][1:].startswith('DotVar')):
            return (KVariable('_' + cellName), KConstant('#Top'))
        return None

    numBytesVars = len([ v for v in collectFreeVars(initConstrainedTerm) if v.startswith('BYTES_') ])
    bytesConstraints = []
    def _parseableBytesTokens(_kast):
        if isKToken(_kast) and _kast['sort'] == 'Bytes' and _kast['token'].startswith('b"') and _kast['token'].endswith('"'):
            bytesVariable = KVariable('BYTES_' + str(len(bytesConstraints) + numBytesVars))
            bytesConstraints.append(boolToMlPred(KApply('_==K_', [bytesVariable, KApply('String2Bytes(_)_BYTES-HOOKED_Bytes_String', [stringToken(_kast['token'][2:-1])])])))
            return bytesVariable
        return _kast

    def _removeCellMapDefinedness(_kast):
        if isKApply(_kast) and _kast['label'].endswith('CellMap:in_keys') and isAnonVariable(_kast['args'][1]):
            return boolToken(False)
        return _kast

    newConstrainedTerm = onCells(_parseableVarNames, initConstrainedTerm)
    newConstrainedTerm = traverseBottomUp(newConstrainedTerm, _parseableBytesTokens)
    newConstrainedTerm = traverseBottomUp(newConstrainedTerm, _removeCellMapDefinedness)
    newConstrainedTerm = buildAssoc(KConstant('#Top'), '#And', [newConstrainedTerm] + bytesConstraints)
    newConstrainedTerm = removeGeneratedCells(newConstrainedTerm)
    return newConstrainedTerm

def kevmProveClaim(directory, mainFileName, mainModuleName, claim, claimId, symbolTable, kevmArgs = [], teeOutput = False, dieOnFail = False):
    tmpClaim  = directory + '/' + claimId.lower() + '-spec.k'
    tmpModule = claimId.upper() + '-SPEC'
    with open(tmpClaim, 'w') as tc:
        claimDefinition = makeDefinition([claim], tmpModule, mainFileName, mainModuleName)
        tc.write(_genFileTimestamp() + '\n')
        tc.write(prettyPrintKast(claimDefinition, symbolTable) + '\n\n')
        tc.flush()
        finalState = kevmProve(mainFileName, tmpClaim, tmpModule, kevmArgs = kevmArgs, teeOutput = teeOutput, dieOnFail = dieOnFail)
        if finalState == KConstant('#Top'):
            return finalState
        finalStates = [ kevmSanitizeConfig(fs) for fs in flattenLabel('#Or', finalState) ]
        return buildAssoc(KConstant('#Bottom'), '#Or', finalStates)

def kevmGetBasicBlockAndNextStates(directory, mainFileName, mainModuleName, claim, claimId, symbolTable, debug = False, maxDepth = 1000):
    logFileName = directory + '/' + claimId.lower() + '-debug.log'
    if os.path.exists(logFileName):
        _notif('Clearing old log file: ' + logFileName)
        os.remove(logFileName)
    nextState  = kevmProveClaim( directory
                               , mainFileName
                               , mainModuleName
                               , claim
                               , claimId
                               , symbolTable
                               , kevmArgs = [ '--haskell-backend-arg' , '--log'
                                            , '--haskell-backend-arg' , logFileName
                                            , '--haskell-backend-arg' , '--log-format'
                                            , '--haskell-backend-arg' , 'oneline'
                                            , '--haskell-backend-arg' , '--enable-log-timestamps'
                                            , '--haskell-backend-arg' , '--log-entries'
                                            , '--haskell-backend-arg' , 'DebugTransition'
                                            , '--branching-allowed'   , '1'
                                            , '--depth'               , str(maxDepth)
                                            ]
                               , teeOutput = debug
                               )
    nextStates = flattenLabel('#Or', nextState)
    _notif('Summarization of ' + claimId + ' resulted in ' + str(len(nextStates)) + ' successor states.')

    branching  = False
    depth      = 0
    finalState = nextStates[0]

    with open(logFileName, 'r') as logFile:
        for line in logFile:
            if line.find('DebugTransition') > 0 and line.find('after  apply axioms:') > 0:
                if branching:
                    break
                else:
                    branching = True
                    depth += 1
            else:
                branching = False

    if branching:
        depth -= 1
        finalState = kevmProveClaim( directory
                                   , mainFileName
                                   , mainModuleName
                                   , claim
                                   , claimId
                                   , symbolTable
                                   , kevmArgs = [ '--depth' , str(depth) ]
                                   , teeOutput = debug
                                   )
        _notif('Found basic block terminal state for ' + claimId + ' at depth ' + str(depth) + '.')
    elif len(nextStates) == 1:
        nextStates = []

    nextStatesWithAddedConstraints = []
    (_, finalConstraint) = splitConfigAndConstraints(finalState)
    finalConstraints     = flattenLabel('#And', finalConstraint)
    for ns in nextStates:
        (_, constraint) = splitConfigAndConstraints(ns)
        constraints     = flattenLabel('#And', constraint)
        newConstraints  = [ c for c in constraints if c not in finalConstraints ]
        nextStatesWithAddedConstraints.append((ns, buildAssoc(KConstant('#Top'), '#And', newConstraints)))

    return ((depth, finalState), nextStatesWithAddedConstraints)

### KEVM Specialization

def abstract(constrainedTerm):

    wordStack     = getCell(constrainedTerm, 'WORDSTACK_CELL')
    wordStackVars = []
    if not isKVariable(wordStack):
        wordStackItems = flattenLabel('_:__EVM-TYPES_WordStack_Int_WordStack', wordStack)
        if not (len(wordStackItems) > 0 and wordStackItems[-1] == KConstant('.WordStack_EVM-TYPES_WordStack')):
            _fatal('Cannot abstract wordstack: ' + str(wordStack))
        wordStackVars  = [ 'W' + str(i) for i in range(len(wordStackItems[0:-1])) ]
        wordStackItems = [ KVariable(v) for v in wordStackVars ]
        wordStack = buildCons(KConstant('.WordStack_EVM-TYPES_WordStack'), '_:__EVM-TYPES_WordStack_Int_WordStack', wordStackItems)

    cellSubst      = { 'WORDSTACK_CELL'  : wordStack
                     , 'GAS_CELL'        : infGas(KVariable('_GAS_CELL'))
                     , 'LOCALMEM_CELL'   : KVariable('_LOCALMEM_CELL')
                     , 'MEMORYUSED_CELL' : KVariable('MEMORYUSED_CELL')
                     }
    newVars        = [ '_GAS_CELL' , '_LOCALMEM_CELL' , 'MEMEORYUSED_CELL' ] + wordStackVars
    newConstraints = [ boolToMlPred(rangeUInt256(KVariable(v))) for v in wordStackVars ]
    newConstraints.append(boolToMlPred(rangeUInt256(KVariable('MEMORYUSED_CELL'))))

    newConstrainedTerm = removeConstraintsFor(newVars, constrainedTerm)
    newConstrainedTerm = applyCellSubst(newConstrainedTerm, cellSubst)
    newConstrainedTerm = removeUselessConstraints(newConstrainedTerm)
    return buildAssoc(KConstant('Top'), '#And', [newConstrainedTerm] + newConstraints)

def subsumes(constrainedTerm1, constrainedTerm2):
    # Could implement this with the search-final-state-matching check used for LLVM backend? Does it work with constraints?
    return getCell(constrainedTerm1, 'PC_CELL') == getCell(constrainedTerm2, 'PC_CELL')

def isTerminal(constrainedTerm):
    return getCell(constrainedTerm, 'K_CELL') == KSequence([KConstant('#halt_EVM_KItem'), ktokenDots])

def buildTerminal(constrainedTerm):
    (config, _) = splitConfigAndConstraints(constrainedTerm)
    cellSubst = { 'K_CELL'  : KSequence([KConstant('#halt_EVM_KItem'), ktokenDots])
                , 'PC_CELL' : KVariable('?_')
                }
    return applyCellSubst(config, cellSubst)

def simplifyBooleanConstraint(constraint):
    constraints    = dedupeClauses(flattenLabel('_andBool_', simplifyBool(constraint)))
    replaces       = []
    newConstraints = []
    for c in constraints:
        if isKApply(c) and c['label'] in [ '_<Int_' , '_<=Int_' ]:
            if c['label'] == '_<=Int_' and c['args'][0] == intToken(0) and isKVariable(c['args'][1]):
                if ltInt(c['args'][1], intToken(2 ** 256)) in constraints:
                    newConstraints.append(rangeUInt256(c['args'][1]))
                    replaces.append((leInt(intToken(0), c['args'][1]), boolToken(True)))
                    replaces.append((ltInt(c['args'][1], intToken(2 ** 256)), boolToken(True)))
                if ltInt(c['args'][1], intToken(2 ** 160)) in constraints:
                    newConstraints.append(rangeAddress(c['args'][1]))
                    replaces.append((leInt(intToken(0), c['args'][1]), boolToken(True)))
                    replaces.append((ltInt(c['args'][1], intToken(2 ** 160)), boolToken(True)))
    newConstraint = buildAssoc(boolToken(True), '_andBool_', constraints + newConstraints)
    for r in replaces:
        newConstraint = replaceAnywhereWith(r, newConstraint)
    return simplifyBool(newConstraint)

### Summarization Utilities

def buildEmptyClaim(initConstrainedTerm, claimId):
    finalConstrainedTerm = buildTerminal(initConstrainedTerm)
    return buildRule(claimId, initConstrainedTerm, finalConstrainedTerm, claim = True, keepVars = collectFreeVars(finalConstrainedTerm))

def writeCFG(cfg):
    cfgLines = [ '// CFG:'
               , '//     states:      ' + ', '.join([str(s) for s in set(list(cfg['graph'].keys()) + cfg['init'] + cfg['terminal'] + cfg['unexplored'] + cfg['stuck'])])
               , '//     init:        ' + ', '.join([str(s) for s in cfg['init']])
               , '//     terminal:    ' + ', '.join([str(s) for s in cfg['terminal']])
               , '//     unexplored:  ' + ', '.join([str(s) for s in cfg['unexplored']])
               , '//     stuck:       ' + ', '.join([str(s) for s in cfg['stuck']])
               , '//     transitions:'
               ]
    for initStateId in cfg['graph']:
        for (finalStateId, constraint, depth) in cfg['graph'][initStateId]:
            cfgLines.append('//         ' + '{0:>3}'.format(initStateId) + ' -> ' + '{0:>3}'.format(finalStateId) + ' [' + '{0:>5}'.format(depth) + ' steps]: ' + ' '.join([c.strip() for c in constraint.split('\n')]))
    return '\n'.join(cfgLines)

### KEVM Summarizer

def buildInitState(contractName, constrainedTerm, schedule = KVariable('SCHEDULE_CELL')):
    accountCell = kevmAccountCell(KVariable('ACCT_ID'), KVariable('ACCT_BALANCE'), KVariable('_ACCT_CODE'), KVariable('_ACCT_STORAGE'), KVariable('_ACCT_ORIGSTORAGE'), KVariable('ACCT_NONCE'))
    cellSubst   = { 'K_CELL'         : KSequence([KConstant('#execute_EVM_KItem'), ktokenDots])
                  , 'ID_CELL'        : KVariable('ACCT_ID')
                  , 'CALLER_CELL'    : KVariable('CALLER_ID')
                  , 'CALLDATA_CELL'  : KVariable('CALLDATA_CELL')
                  , 'GAS_CELL'       : infGas(KVariable('_GAS_CELL'))
                  , 'PC_CELL'        : KToken('0', 'Int')
                  , 'WORDSTACK_CELL' : KConstant('.WordStack_EVM-TYPES_WordStack')
                  , 'LOCALMEM_CELL'  : KVariable('LOCALMEM_CELL')
                  , 'ACCOUNTS_CELL'  : KApply('_AccountCellMap_', [KApply('AccountCellMapItem', [KApply('<acctID>', [KVariable('ACCT_ID')]), accountCell]), KVariable('_ACCOUNTS')])
                  }
    constraints = [ boolToMlPred(rangeAddress(KVariable('ACCT_ID')))
                  , boolToMlPred(rangeAddress(KVariable('CALLER_ID')))
                  , boolToMlPred(rangeUInt256(KVariable('ACCT_BALANCE')))
                  , boolToMlPred(rangeUInt256(KVariable('ACCT_NONCE')))
                  , boolToMlPred(ltInt(sizeByteArray(KVariable('CALLDATA_CELL')), intToken(2 ** 256)))
                  ]
    return buildAssoc(KConstant('#Top'), '#And', [applyCellSubst(constrainedTerm, cellSubst)] + constraints)

def kevmWriteStateToFile(directory, contractName, stateId, state, symbolTable):
    stateFileName = contractName.lower() + '-state-' + stateId
    _notif('Writing state file: ' + stateFileName)
    with open(directory + '/' + stateFileName + '.json', 'w') as f:
        f.write(json.dumps(state, indent = 2))
    with open(directory + '/' + stateFileName + '.k', 'w') as f:
        f.write(_genFileTimestamp() + '\n')
        f.write(prettyPrintKast(state, symbolTable))

def kevmSummarize( directory
                 , initState
                 , mainFileName
                 , mainModuleName
                 , contractName
                 , symbolTable
                 , intermediateClaimsFile
                 , intermediateClaimsModule
                 , debug = False
                 , verify = False
                 , maxBlocks = None
                 , maxDepth = 1000
                 , startOffset = 0
                 ):

    frontier          = [(startOffset + i, ct) for (i, ct) in enumerate(flattenLabel('#Or', initState))]
    seenStates        = []
    newClaims         = []
    newRules          = []
    cfg               = {}
    cfg['graph']      = {}
    cfg['init']       = [i for (i, _) in frontier]
    cfg['terminal']   = []
    cfg['unexplored'] = [i for (i, _) in frontier]
    cfg['stuck']      = []
    nextStateId       = startOffset + len(frontier)
    writtenStates     = []

    while len(frontier) > 0 and (maxBlocks is None or len(newClaims) < maxBlocks):
        (initStateId, initState) = frontier.pop(0)
        initState                = abstract(initState)
        seenStates.append((initStateId, initState))
        if initStateId not in writtenStates:
            kevmWriteStateToFile(directory, contractName, str(initStateId), initState, symbolTable)
            writtenStates.append(initStateId)
        claimId                                = contractName.upper() + '-GEN-' + str(initStateId) + '-TO-MAX' + str(maxDepth)
        emptyClaim                             = buildEmptyClaim(initState, claimId)
        ((finalDepth, finalState), nextStates) = kevmGetBasicBlockAndNextStates( directory
                                                                               , mainFileName
                                                                               , mainModuleName
                                                                               , emptyClaim
                                                                               , claimId
                                                                               , symbolTable
                                                                               , debug = debug
                                                                               , maxDepth = maxDepth
                                                                               )
        finalStateId = nextStateId
        nextStateId  = nextStateId + 1
        basicBlockId = contractName.upper() + '-BASIC-BLOCK-' + str(initStateId) + '-TO-' + str(finalStateId)
        if finalStateId not in writtenStates:
            kevmWriteStateToFile(directory, contractName, str(finalStateId), finalState, symbolTable)
            writtenStates.append(finalStateId)
        cfg['graph'][initStateId] = [(finalStateId, printConstraint(KConstant('#Top'), symbolTable), finalDepth)]
        if isTerminal(finalState):
            cfg['terminal'].append(finalStateId)
        else:
            if len(nextStates) == 0:
                cfg['stuck'].append(finalStateId)
            cfg['graph'][finalStateId] = []

        newClaim = buildRule(basicBlockId, initState, finalState, claim = True)
        newClaims.append(newClaim)

        if not isTerminal(finalState):
            for (i, (ns, newConstraint)) in enumerate(nextStates):
                subsumed = False
                for (j, seen) in seenStates:
                    if subsumes(ns, seen):
                        subsumed = True
                        cfg['graph'][finalStateId].append((j, printConstraint(newConstraint, symbolTable), 1))
                if not subsumed:
                    stateId     = nextStateId
                    nextStateId = nextStateId + 1
                    if stateId not in writtenStates:
                        kevmWriteStateToFile(directory, contractName, str(stateId), ns, symbolTable)
                        writtenStates.append(stateId)
                    cfg['graph'][finalStateId].append((stateId, printConstraint(newConstraint, symbolTable), 1))
                    frontier.append((stateId, ns))
            cfg['unexplored'] = [i for (i, _) in frontier]

        if verify:
            kevmProveClaim( directory
                          , mainFileName
                          , mainModuleName
                          , newClaim
                          , basicBlockId
                          , symbolTable
                          , dieOnFail = True
                          )
            _notif('Verified claim: ' + basicBlockId)
        newRule = buildRule(basicBlockId, initState, finalState, claim = False, priority = 35)
        newRules.append(newRule)

        with open(intermediateClaimsFile, 'w') as intermediate:
            claimDefinition = makeDefinition(newClaims, intermediateClaimsModule, mainFileName, mainModuleName)
            intermediate.write(_genFileTimestamp() + '\n')
            intermediate.write(prettyPrintKast(claimDefinition, symbolTable) + '\n\n')
            intermediate.write(writeCFG(cfg) + '\n')
            intermediate.flush()
            _notif('Wrote updated claims file: ' + intermediateClaimsFile)

    return (newRules, cfg)

### Main Functionality

summarizeArgs = pykCommandParsers.add_parser('summarize', help = 'Given a disjunction of states, build the true halting spec for each state.')
summarizeArgs.add_argument('init-term' , type = argparse.FileType('r'), help = 'JSON representation of initial state.')
summarizeArgs.add_argument('contract-name' , type = str, help = 'Name of contract to summarize.')
summarizeArgs.add_argument('main-module-file' , type = str, help = 'Name of main verification file.')
summarizeArgs.add_argument('main-module-name' , type = str, help = 'Name of main verification module.')
summarizeArgs.add_argument('-n', '--max-blocks', type = int, nargs = '?', help = 'Maximum number of basic block summarize to generate.')
summarizeArgs.add_argument('--resume-from-state', type = int, nargs = '?', help = 'Start from saved state file in summarization directory.')
summarizeArgs.add_argument('--debug', default = False, action = 'store_true', help = 'Keep temporary files around.')
summarizeArgs.add_argument('--verify',    default = True,  action = 'store_true',  help = 'Prove generated claims before outputting them.')
summarizeArgs.add_argument('--no-verify', dest = 'verify', action = 'store_false', help = 'Do not prove generated claims before outputting them.')
summarizeArgs.add_argument('--use-schedule', type = str, help = 'Name of the Ethereum schedule to use for verification.')
summarizeArgs.add_argument('-o', '--output', type = argparse.FileType('w'), default = '-')

def kevmPykMain(args, kompiled_dir):

    if args['command'] == 'summarize':

        json_definition = readKastTerm(kompiled_dir + '/compiled.json')
        symbolTable     = kevmSymbolTable(json_definition, opinionated = True)

        mainFileName             = args['main-module-file']
        directory                = '/'.join(mainFileName.split('/')[0:-1])
        mainModuleName           = args['main-module-name']
        contractName             = args['contract-name']
        intermediateClaimsFile   = directory + '/' + contractName.lower() + '-basic-blocks-spec.k'
        intermediateClaimsModule = contractName.upper() + '-BASIC-BLOCKS-SPEC'
        summaryRulesModule       = contractName.upper() + '-BASIC-BLOCKS'
        maxBlocks                = None if 'max_blocks' not in args else args['max_blocks']
        resumeFromState          = None if 'max_blocks' not in args else args['resume_from_state']

        if resumeFromState is None:
            initState = buildInitState(contractName, json.loads(args['init-term'].read())['term'])
        else:
            with open(directory + '/' + contractName.lower() + '-state-' + str(args['resume_from_state']) + '.json', 'r') as resumeState:
                initState = json.loads(resumeState.read())
        initState = kevmSanitizeConfig(initState)

        if 'use_schedule' in args and args['use_schedule'] is not None:
            initState = setCell(initState, 'SCHEDULE_CELL', KConstant(args['use_schedule'] + '_EVM'))

        (newRules, cfg)   = kevmSummarize( directory
                                         , initState
                                         , mainFileName
                                         , mainModuleName
                                         , contractName
                                         , symbolTable
                                         , intermediateClaimsFile
                                         , intermediateClaimsModule
                                         , debug = args['debug']
                                         , verify = args['verify']
                                         , maxBlocks = maxBlocks
                                         , startOffset = resumeFromState if resumeFromState is not None else 0
                                         )
        summaryDefinition = makeDefinition(newRules, summaryRulesModule, mainFileName, mainModuleName)

        args['output'].write(_genFileTimestamp() + '\n')
        args['output'].write(prettyPrintKast(summaryDefinition, symbolTable) + '\n\n')
        args['output'].write(writeCFG(cfg) + '\n')
        args['output'].flush()

if __name__ == '__main__':
    main(pykArgs, extraMain = kevmPykMain)
