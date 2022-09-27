#!/bin/bash

kast --input kore --output json --definition $1 /dev/stdin | jq .term | pyk print $1 /dev/stdin --omit-labels $2
