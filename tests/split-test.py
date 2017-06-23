#!/usr/bin/env python


import sys
import json
import os

# Example usage: tests/ethereum-tests/VMTests/abc.json tests/test-devel/VMTests/abc/ <template_file> 
source_file = sys.argv[1]
target_dir = sys.argv[2]

with open (source_file, "r") as source:
    original_test = json.load(source)
    for subtest in original_test.keys():
        target_file = os.path.join(target_dir, subtest + ".json")
        with open (target_file, "w+") as target:
            json.dump({ subtest: original_test[subtest] }, target, indent=4)
        if (len(sys.argv) == 4):
            target_out_file = os.path.join(target_dir, subtest + ".json.out")
            template_file = sys.argv[3] 
            with open (target_out_file, "w+") as outfile:
                with open (template_file, "r") as template:
                    outfile.write(template.read())


