#!/usr/bin/env python3.6

import sys
import os
import re
import configparser

def subst(text, key, val):
    return re.compile('{' + key.upper() + '}').sub(val, text)

def gen(spec, ini):
    config = configparser.ConfigParser()
    config.read(ini)
    origspec = spec
    for sec in ['DEFAULT'] if not config.sections() else config.sections():
        spec = origspec
        for key in config[sec]:
            spec = subst(spec, key, config[sec][key].strip()) 
        spec = subst(spec, 'module', os.path.splitext(os.path.basename(ini))[0].upper())
        fout = open(os.path.splitext(ini)[0] + ('' if sec == 'DEFAULT' else sec) + "-spec.k", "w")
        fout.write(spec)
        fout.close()

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print("usage: <cmd> <spec> <ini>")
        sys.exit(1)
    with open(sys.argv[1], "r") as fin:
        spec = fin.read()
    gen(spec, sys.argv[2])
