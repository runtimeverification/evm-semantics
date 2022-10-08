#!/bin/bash

kast --input kore --output json --definition $1 /dev/stdin --bison-stack-max-depth 100000000 | jq --stream 'fromstream(1|truncate_stream(inputs|select(.[0][0] == "term")))' | /home/ja/.cache/pypoetry/virtualenvs/pyk-6o1ctocz-py3.10/bin/pyk print $1 /dev/stdin --keep-cells $2
