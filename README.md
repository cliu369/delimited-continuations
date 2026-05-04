## Compilation

To generate/update the `RocqMakefile` from `_RocqProject`:

`rocq makefile -f _RocqProject -o RocqMakefile`

Then, to compile/check all proof scripts listed in `_CoqProject`:

`make -f RocqMakefile all`

Compatibility tested with Rocq `9.10.0`
