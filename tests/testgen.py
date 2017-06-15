#!/usr/bin/env python

import sys
import json
import os

if __name__ == "__main__":
    with open (sys.argv[1], "r") as f:
        bpath = os.path.dirname(f.name)
        metainfo = json.load(f)
        for metaobj in metainfo:
           fname = metaobj["filename"] + ".kson"
           with open(os.path.join(bpath, fname), "w+") as outfile:
                   json.dump(metaobj["contents"], outfile, indent=4)
            
