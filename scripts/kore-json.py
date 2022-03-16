#!/usr/bin/env python3

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

def print_direct(s):
  sys.stdout.write(s)

def print_config_map_entry(k, v, vsort, vprint):
  sys.stdout.write("Lbl'UndsPipe'-'-GT-Unds'{}(")
  print_sort_injection("KConfigVar", "KItem", k, print_k_config_var)
  sys.stdout.write(",")
  print_sort_injection(vsort, "KItem", v, vprint)
  sys.stdout.write(")")

sys.stdout.write("LblinitGeneratedTopCell{}(Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(Lbl'Unds'Map'Unds'{}(Lbl'Stop'Map{}(),")
print_config_map_entry("PGM", data, "JSON", print_kast)
sys.stdout.write("),")
print_config_map_entry("SCHEDULE", sys.argv[2], "Schedule", print_direct)
sys.stdout.write("),")
print_config_map_entry("MODE", sys.argv[3], "Mode", print_direct)
sys.stdout.write("),")
print_config_map_entry("CHAINID", sys.argv[4], "Int", print_direct)
sys.stdout.write("))\n")
sys.stdout.write("\n")
sys.stdout.flush()
