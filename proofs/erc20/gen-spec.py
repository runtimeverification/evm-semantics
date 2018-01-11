#!/usr/bin/env python3.6

import sys
import os
import re
import configparser

def subst(text, key, val):
    return re.compile('{' + key.upper() + '}').sub(val, text)

def gen(template, ini):
    config = configparser.ConfigParser()
    config.read(ini)
    sections = ['DEFAULT'] if not config.sections() else config.sections()
    for sec in sections:
        genspec = template
        for key in config[sec]:
            genspec = subst(genspec, key, config[sec][key].strip())
        genspec = subst(genspec, 'module', os.path.splitext(os.path.basename(ini))[0].upper())
        fout = open(os.path.splitext(ini)[0] + ('' if sec == 'DEFAULT' else sec) + "-spec.k", "w")
        fout.write(genspec)
        fout.close()

if __name__ == '__main__':
    if len(sys.argv) < 3:
        print("usage: <cmd> <template> <ini>")
        sys.exit(1)
    template = open(sys.argv[1], "r").read()
    gen(template, sys.argv[2])
