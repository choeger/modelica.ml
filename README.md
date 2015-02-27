modelica.ml
===========

Modelica frontend implemented in OCaml

Modelica (http://modelica.org) is an open equation-based modeling language.
This project implements a Modelica frontend  (i.e. abstract syntax tree + 
parsing + lexing + some analysis) as a OCaml library.


## Status

This library is currently in its infancy. Right now, only parsing and pretty
printing are implemented. Even the API is subject to change. However, it might
already be useful for someone, so I am publishing it.

## Installing via opam

Soon to come ...

## API Documentation

Version 0.1.1: http://choeger.github.io/apidoc/modelica_ml-0.1.1/

## Building

This is a package built with oasis, so the following sequence should build it:

### Dependencies:

```sh
opam install ppx_deriving batteries menhir oUnit ANSITerminal ppx_deriving_yojson sedlex
```

### Configuration

```sh
oasis setup
./configure --enable-tests
```

### Compilation

```sh
make
```



