# Mechanization of Delimited Continuations 

Based on https://github.com/TiarkRompf/types-and-proofs.

## Compilation

To generate/update the `RocqMakefile` from `_RocqProject`:

`rocq makefile -f _RocqProject -o RocqMakefile`

Then, to compile/check all proof scripts listed in `_RocqProject_`:

`make -f RocqMakefile all`

Compatibility tested with Rocq `9.10.0`.
