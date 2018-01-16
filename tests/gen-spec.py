#!/usr/bin/env python3.6

import sys
import os
import re
import configparser

def subst(text, key, val):
    return re.compile('{' + key.upper() + '}').sub(val, text)

def gen(template, ini, outdir):
    config = configparser.ConfigParser()
    config.read(ini)
    sections = ['DEFAULT'] if not config.sections() else config.sections()
    ini_basename = os.path.splitext(os.path.basename(ini))[0]
    out_prefix = outdir + ini_basename
    for sec in sections:
        genspec = template
        for key in config[sec]:
            genspec = subst(genspec, key, config[sec][key].strip())
        genspec = subst(genspec, 'module', ini_basename.upper())
        fout = open(out_prefix + ('' if sec == 'DEFAULT' else sec) + "-spec.k", "w")
        fout.write(genspec)
        fout.close()

    # touch timestamp file for simplifying makefile
    timestamp_file = out_prefix + '.timestamp'
    with open(timestamp_file, 'a'):
        os.utime(timestamp_file, None)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        print("usage: <cmd> <template> <ini> <outdir>")
        sys.exit(1)
    template = open(sys.argv[1], "r").read()
    gen(template, sys.argv[2], sys.argv[3])
