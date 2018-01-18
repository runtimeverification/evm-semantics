#!/usr/bin/env python3.6

import sys
import re
import configparser

def subst(text, key, val):
#    return re.compile('{' + key.upper() + '}').sub(val, text)
    return text.replace('{' + key + '}', val)

def safe_get(config, section):
    if section in config:
        return config[section]
    else:
        return {}

def inherit_get(config, section):
    if not section:
        return safe_get(config, 'DEFAULT')
    else:
        parent = inherit_get(config, '-'.join(section.split('-')[:-1]))
        current = safe_get(config, section)
        merged = {**parent, **current}
        for key in list(merged.keys()):
            if key.startswith('+'):
                merged[key[1:]] += merged[key]
                del merged[key]
        return merged

def gen(template, ini1, ini2, name):
    config1 = configparser.ConfigParser(comment_prefixes=(';'))
    config1.read(ini1)
    config2 = configparser.ConfigParser(comment_prefixes=(';'))
    config2.read(ini2)
    genspec = template
    config = {**inherit_get(config1, name),
              **config2['DEFAULT'],
              **{'module': name.upper()}}
    for key in config:
        genspec = subst(genspec, key, config[key].strip())
    print(genspec)

if __name__ == '__main__':
    if len(sys.argv) != 5:
        print("usage: <cmd> <template> <ini1> <ini2> <name>")
        sys.exit(1)
    template = open(sys.argv[1], "r").read()
    gen(template, sys.argv[2], sys.argv[3], sys.argv[4])
