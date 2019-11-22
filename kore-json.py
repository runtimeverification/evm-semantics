#!/usr/bin/env python3

import json
import sys
from collections import OrderedDict

filename = sys.argv[1]

with open(filename) as data_file:    
    data = json.load(data_file, object_pairs_hook=OrderedDict)

def escape(data):
  return data.encode('unicode_escape')

def print_kast(data, sort="SortJSON"):
  if isinstance(data, list):
    sys.stdout.write("Lbl'LSqBUndsRSqBUnds'JSON'Unds'JSON'Unds'JSONList{}(")
    for elem in data:
      sys.stdout.write("Lbl'UndsCommUndsUnds'JSON'Unds'JSONList'Unds'JSON'Unds'JSONList{}(")
      print_kast(elem)
      sys.stdout.write(',')
    sys.stdout.write("Lbl'Stop'List'LBraQuotUndsCommUndsUnds'JSON'Unds'JSONList'Unds'JSON'Unds'JSONList'QuotRBraUnds'JSONList{}()")
    for elem in data:
      sys.stdout.write(')')
    sys.stdout.write(')')
  elif isinstance(data, OrderedDict):
    sys.stdout.write("Lbl'LBraUndsRBraUnds'JSON'Unds'JSON'Unds'JSONList{}(")
    for key, value in data.items():
      sys.stdout.write("Lbl'UndsCommUndsUnds'JSON'Unds'JSONList'Unds'JSON'Unds'JSONList{}(Lbl'UndsColnUndsUnds'JSON'Unds'JSON'Unds'JSONKey'Unds'JSON{}(")
      print_kast(key, "SortJSONKey")
      sys.stdout.write(',')
      print_kast(value)
      sys.stdout.write('),')
    sys.stdout.write("Lbl'Stop'List'LBraQuotUndsCommUndsUnds'JSON'Unds'JSONList'Unds'JSON'Unds'JSONList'QuotRBraUnds'JSONList{}()")
    for key in data:
      sys.stdout.write(')')
    sys.stdout.write(')')
  elif isinstance(data, str) or isinstance(data, unicode):
    sys.stdout.write("inj{SortString{}, " + sort + "{}}(\dv{SortString{}}("),
    sys.stdout.write(json.dumps(data))
    sys.stdout.write('))')
  elif isinstance(data, long) or isinstance(data, int):
    sys.stdout.write("inj{SortInt{}, " + sort + '{}}(\dv{SortInt{}}("'),
    sys.stdout.write(str(data))
    sys.stdout.write('"))')
  else:
    sys.stdout.write(type(data))
    raise AssertionError

def print_klabel(s):
  print("Lbl" + s.replace("_", "'Unds'").replace("`", "").replace("(.KList)", "{}"), end=' ')

print("LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}(\"$PGM\")),inj{SortJSON{}, SortKItem{}}(", end=' ')
print_kast(data)
print("))),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}(\"$SCHEDULE\")),inj{SortSchedule{}, SortKItem{}}(", end=' ')
print_klabel(sys.argv[2])
print("()))),Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortKConfigVar{}, SortKItem{}}(\dv{SortKConfigVar{}}(\"$MODE\")),inj{SortMode{}, SortKItem{}}(", end=' ')
print_klabel(sys.argv[3])
print("()))))")
print()
