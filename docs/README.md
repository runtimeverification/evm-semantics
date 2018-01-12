The EVM Jello Paper
===================

The Jello Paper is documentation for the EVM generated from the `KEVM project <https://github.com/kframework/evm-semantics>`_.
The KEVM improves on the `Yellow Paper <http://yellowpaper.io.>` by being executable, which provides a full reference EVM interpreter.
This is useful for testing contracts, analyzing gas usage, verifying contract correctness, and a wide range of other tasks.

To generate the Jello Paper HTML pages, call `make` in this directory.
This requires that the `K Pygments Package <https://github.com/kframework/k-editor-support>` is installed.

.. toctree::

   :maxdepth: 2
   evm
   driver
   verification
   data
   analysis
   krypto
   issues
