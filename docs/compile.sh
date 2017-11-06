#!/bin/sh
pandoc -o analysis.rst  analysis.md 
pandoc -o data.rst data.md
pandoc -o ethereum.rst ethereum.md
pandoc -o evm.rst evm.md
pandoc -o issues.rst issues.md
pandoc -o krypto.rst krypto.md
pandoc -o verification.rst verification.md
sed -i 's/code:: k/code-block:: k/g' *.rst

