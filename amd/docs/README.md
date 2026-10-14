# Guide

1. [Getting started](guide/01-getting-started.md): build, evaluate a block, read the results.
2. [The paper's notation in Lean](guide/02-notation.md): every symbol and feature-table row.
3. [The three architectures](guide/03-architectures.md): CDNA 1, CDNA 2, CDNA 3 and their theorems.
4. [The independent specification](guide/04-specification.md): what it transcribes and how it is
   connected to the model.
5. [Tests](../tests/README.md): the paper's test vectors and the trust audit.
6. [Differential testing](differential.md): comparison with the authors' MATLAB models and, on
   binary8, with MMA-Sim.
7. [FloatLib implementation](../floatlib-port/README.md): a second implementation on FloatLib
   and its equivalence proof.

[Paper notes](paper-notes.md) records modeling choices the paper leaves open, the points where
the regression suite and the paper's prose differ, and differences from the MATLAB models.
