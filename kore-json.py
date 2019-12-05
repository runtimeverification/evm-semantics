#!/usr/bin/env python

import json
import sys
from collections import OrderedDict

filename = sys.argv[1]

with open(filename) as data_file:    
    data = json.load(data_file, object_pairs_hook=OrderedDict)

def escape(data):
  return data.encode('unicode_escape')

def print_int(data):
  sys.stdout.write("\dv{SortInt{}}(\"")
  sys.stdout.write(data)
  sys.stdout.write("\")")

def print_string(data):
  sys.stdout.write("\dv{SortString{}}(")
  sys.stdout.write(json.dumps(data))
  sys.stdout.write(")")

def print_k_config_var(data):
  sys.stdout.write("\dv{SortKConfigVar{}}(\"$" + data + "\")")

def print_sort_injection(s1, s2, data, printer):
  sys.stdout.write("inj{Sort" + s1 + "{}, " + "Sort" + s2 + "{}}(")
  printer(data)
  sys.stdout.write(")")

def print_kast(data, sort="JSON"):
  if isinstance(data, list):
    sys.stdout.write("LblJSONList{}(")
    for elem in data:
      sys.stdout.write("LblJSONs{}(")
      print_kast(elem)
      sys.stdout.write(',')
    sys.stdout.write("Lbl'Stop'List'LBraQuot'JSONs'QuotRBraUnds'JSONs{}()")
    for elem in data:
      sys.stdout.write(')')
    sys.stdout.write(')')
  elif isinstance(data, OrderedDict):
    sys.stdout.write("LblJSONObject{}(")
    for key, value in data.items():
      sys.stdout.write("LblJSONs{}(LblJSONEntry{}(")
      print_kast(key, sort = "JSONKey")
      sys.stdout.write(',')
      print_kast(value)
      sys.stdout.write('),')
    sys.stdout.write("Lbl'Stop'List'LBraQuot'JSONs'QuotRBraUnds'JSONs{}()")
    for key in data:
      sys.stdout.write(')')
    sys.stdout.write(')')
  elif isinstance(data, str) or isinstance(data, unicode):
    print_sort_injection("String", sort, data, print_string)
  elif isinstance(data, long) or isinstance(data, int):
    print_sort_injection("Int", sort, data, print_int)
  else:
    sys.stdout.write(type(data))
    raise AssertionError

def print_klabel(s):
  sys.stdout.write("Lbl" + s.replace("_", "'Unds'").replace("`", "").replace("(.KList)", "{}") + "()")

sys.stdout.write("LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),Lbl'UndsPipe'-'-GT-Unds'{}(")
print_sort_injection("KConfigVar", "KItem", "PGM", print_k_config_var)
sys.stdout.write(",")
print_sort_injection("JSON", "KItem", data, print_kast)
sys.stdout.write(")),Lbl'UndsPipe'-'-GT-Unds'{}(")
print_sort_injection("KConfigVar", "KItem", "SCHEDULE", print_k_config_var)
sys.stdout.write(",")
print_sort_injection("Schedule", "KItem", sys.argv[2], print_klabel)
sys.stdout.write(")),Lbl'UndsPipe'-'-GT-Unds'{}(")
print_sort_injection("KConfigVar", "KItem", "MODE", print_k_config_var)
sys.stdout.write(",")
print_sort_injection("Mode", "KItem", sys.argv[3], print_klabel)
sys.stdout.write(")))\n")
sys.stdout.write("\n")
sys.stdout.flush()
