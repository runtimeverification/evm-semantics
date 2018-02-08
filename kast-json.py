#!/usr/bin/env python

import json
import sys
from collections import OrderedDict

filename = sys.argv[1]

with open(filename) as data_file:    
    data = json.load(data_file, object_pairs_hook=OrderedDict)

def escape(data):
  return data.encode('unicode_escape')

def print_kast(data):
  if isinstance(data, list):
    sys.stdout.write('`[_]_EVM-DATA`(')
    for elem in data:
      sys.stdout.write('`_,__EVM-DATA`(')
      print_kast(elem)
      sys.stdout.write(',')
    sys.stdout.write('`.List{"_,__EVM-DATA"}`(.KList)')
    for elem in data:
      sys.stdout.write(')')
    sys.stdout.write(')')
  elif isinstance(data, OrderedDict):
    sys.stdout.write('`{_}_EVM-DATA`(')
    for key, value in data.items():
      sys.stdout.write('`_,__EVM-DATA`(`_:__EVM-DATA`(')
      print_kast(key)
      sys.stdout.write(',')
      print_kast(value)
      sys.stdout.write('),')
    sys.stdout.write('`.List{"_,__EVM-DATA"}`(.KList)')
    for key in data:
      sys.stdout.write(')')
    sys.stdout.write(')')
  elif isinstance(data, str) or isinstance(data, unicode):
    sys.stdout.write('#token('),
    sys.stdout.write(json.dumps(json.dumps(data)))
    sys.stdout.write(',"String")')
  elif isinstance(data, long) or isinstance(data, int):
    sys.stdout.write('#token("'),
    sys.stdout.write(str(data))
    sys.stdout.write('","Int")')
  else:
    sys.stdout.write(type(data))
    raise AssertionError

print_kast(data)
print
