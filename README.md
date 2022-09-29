# TLA in Coq

[![CI](https://github.com/tchajed/coq-tla/actions/workflows/build.yml/badge.svg)](https://github.com/tchajed/coq-tla/actions/workflows/build.yml)

Embedding TLA in Coq. The goal is to better understand how TLA can be used for
liveness reasoning especially, by playing around with the proof system and
trying out small examples with full proofs. Automation is just adequate here to
get work done, but not suitable for large systems or complex temporal reasoning
with many hypotheses.

Documentation compiled with Alectryon is automatically generated. Some good
places to start are the [basic
definitions](https://tchajed.github.io/coq-tla/defs.html) and a simple [example
of liveness](https://tchajed.github.io/coq-tla/examples/hello_liveness.html) for
a toy transition system.

The TLA definitions and rules owe a lot to the classic paper ["The Temporal
Logic of Actions"](https://dl.acm.org/doi/pdf/10.1145/177492.177726).
