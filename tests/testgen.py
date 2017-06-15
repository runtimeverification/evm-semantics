#!/usr/bin/env python

import sys
import json
import os

if __name__ == "__main__":
    with open (sys.argv[1], "r") as f:
        bpath = os.path.dirname(f.name)
        metainfo = json.load(f)
        for metaobj in metainfo:
           mfname = metaobj["filename"] + ".kson"
           rfname = metaobj["filename"] + ".kson.out"
           with open(os.path.join(bpath, mfname), "w+") as outfile:
               json.dump(metaobj["contents"], outfile, indent=4)
           with open(os.path.join(bpath, rfname), "w+") as resfile:
               #Hack to generate the output files. 
               with open(sys.argv[2], "r") as template:
                   resfile.write(template.read())

