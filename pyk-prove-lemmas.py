#!/usr/bin/env bash

from pyk import *
import sys

input_defn = sys.argv[1]
module_names = sys.argv[2].split(',')
requires_names = sys.argv[3].split(',')
output_dir = sys.argv[4]

proving_definition = readKastTerm(input_defn)
symbolTable = buildSymbolTable(proving_definition)
symbolTable['_++_WS']         = lambda ws0, ws1: '( ' + ws0 + ' ++ ' + ws1 + ' )'
symbolTable['byteArraySlice'] = lambda ba, start, width: '( ' + ba + ' [ ' + start + ' .. ' + width + ' ] )'
symbolTable['mapWriteBytes']  = lambda mem, idx, val: mem + ' [ ' + idx + ' := (' + val + '):ByteArray ]'
symbolTable['runLemma']       = lambda k: 'runLemma(' + k + ')'
symbolTable['doneLemma']      = lambda k: 'doneLemma(' + k + ')'

modules = [ m for m in proving_definition['modules'] if m['name'] in module_names ]

imports = []
for m in proving_definition['modules']:
    if m['name'] in module_names:
        for i in m['imports']:
            if not ('$' in i or i in module_names):
                imports.append(i)
imports = list(set(imports))

def cleanRule(body, requires, ensures, att = None):
    subst = { '_' + str(i): KVariable('_') for i in range(10) }
    body = substitute(body, subst)
    requires = requires if not requires == KToken('true', 'Bool') else None
    ensures = ensures if not ensures == KToken('true', 'Bool') else None
    return KRule(body, requires = requires, ensures = ensures, att = att)

def cleanClaim(body, requires, ensures, att = None):
    r = cleanRule(body, requires, ensures, att = att)
    return KClaim(r['body'], requires = r['requires'], ensures = r['ensures'], att = r['att'])

other_sentences = []
rules = []
for m in modules:
    for s in m['localSentences']:
        if isKRule(s):
            if s['att'] is None or not 'trusted' in s['att']['att'].keys():
                rules.append(s)
            else:
                other_sentences.append(cleanRule(s['body'], s['requires'], s['ensures'], att = KAtt({'smt-lemma': '', 'simplification': '', 'trusted': ''})))
        else:
            other_sentences.append(s)

other_sentences.append(KProduction([KTerminal('runLemma') , KTerminal('('), KNonTerminal(KSort('K')), KTerminal(')')], KSort('KItem'), att = KAtt({ 'klabel': 'runLemma' , 'symbol': '' })))
other_sentences.append(KProduction([KTerminal('doneLemma'), KTerminal('('), KNonTerminal(KSort('K')), KTerminal(')')], KSort('KItem'), att = KAtt({ 'klabel': 'doneLemma', 'symbol': '' })))
other_sentences.append(KRule(KApply('<k>', [KRewrite(KApply('runLemma', [KVariable('K')]), KApply('doneLemma', [KVariable('K')]))])))

modules = []
main_module_name = 'MAIN-MODULE'
main_module = KFlatModule(main_module_name, imports, other_sentences)
main_defn = KDefinition(main_module_name, [main_module], requires = [KRequire(n) for n in requires_names], att = proving_definition['att'])
defns = { 'main-module.k': main_defn }
for i in range(len(rules)):
    defn_module_name = 'VERIFICATION'
    spec_module_name = 'CLAIM-' + str(i) + '-SPEC'
    rule = rules[i]
    other_rules = rules[0:i] + rules[i+1:len(rules)]
    other_lemmas = [ cleanRule(r['body'], r['requires'], r['ensures'], att = KAtt({'smt-lemma': '', 'simplification': ''})) for r in other_rules ]
    defn_module = KFlatModule(defn_module_name, [main_module_name], other_lemmas)
    spec_rule_body = KApply('<k>', [KRewrite(KApply('runLemma', [rule['body']['lhs']]), KApply('doneLemma', [rule['body']['rhs']]))])
    spec_module = KFlatModule(spec_module_name, [defn_module_name], [cleanClaim(spec_rule_body, rule['requires'], rule['ensures'])])
    spec_defn = KDefinition(defn_module_name, [defn_module, spec_module], requires = [KRequire('main-module.k')])
    defns[spec_module_name.lower() + '.k'] = spec_defn

for defn in defns.keys():
    with open(output_dir + defn, 'w') as out:
        out.write(prettyPrintKast(defns[defn], symbolTable))
