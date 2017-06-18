#!/usr/bin/env python


import sys
import json

# Example usage: tests/ethereum-tests/VMTests/abc.json tests/test-devel/VMTests/abc/
source_file=sys.argv[1]
target_dir=sys.argv[2]

with open (source_file, "r") as source:
    original_test = json.load(source)
    for subtest in original_test.iterkeys():
        target_file=target_dir + "/" + subtest + ".json"
        with open (target_file, "w+") as target:
            json.dump({ subtest: original_test[subtest] }, target, indent=4)
