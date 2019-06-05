JelloPaper: Human Readable Semantics of EVM in K
================================================

The Jello Paper is an attempt at defining the EVM semantics using the
`KEVM project <https://github.com/kframework/evm-semantics>`_. Unlike
the `Yellow Paper <http://yellowpaper.io/>`_, the Jello Paper is an
executable semantics, and can provide a full EVM interpreter usable for
testing contracts, analyzing gas usage, verifying contracts correct, and
a wide range of other tasks as specified in `the technical report on
KEVM <https://www.ideals.illinois.edu/handle/2142/97207>`_.

The KEVM semantics described by the Jello Paper is the first
machine-executable, mathematically formal, human readable, and
complete semantics of the EVM. KEVM is capable of passing the full EVM
`VMTests <https://github.com/ethereum/tests/tree/develop/VMTests>`_
and `GeneralStateTests
<https://github.com/ethereum/tests/tree/develop/GeneralStateTests>`_
testing suites, and can also be used in `smart contract formal
verification
<https://github.com/runtimeverification/verified-smart-contracts>`_,
debugging, and more.  The Jello Paper (this document) is automatically
generated from the `K definition of the KEVM semantics
<https://github.com/kframework/evm-semantics>`_.

Start by choosing any section below or in the sidebar.

.. toctree::
   README
   evm
   evm-node
   driver
   edsl
   network
   data
   analysis
   krypto
   issues


Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
* :ref:`search`


