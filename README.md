# Iris Tactics for SSL

Coq tactics for the [Iris](https://gitlab.mpi-sws.org/iris/iris) framework to support certified program synthesis using [SuSLik](https://github.com/TyGuS/suslik).

## Requirements

* [Coq](https://coq.inria.fr/download) (>= "8.11.2" & < "8.13~")
* [CoqHammer](https://coqhammer.github.io)

## Installing

### With OPAM

We recommend installing with [OPAM](https://opam.ocaml.org/doc/Install.html).

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq coq-iris.dev.2021-02-24.0.ffcaed52 coq-iris-heap-lang coq-ssl-iris
```

### Manually

Run `make clean && make install` in the project root.

