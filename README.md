# Mechanization of Delimited Continuations 

Based on https://github.com/TiarkRompf/types-and-proofs.

## Compilation

To generate/update the `RocqMakefile` from `_RocqProject`:

`rocq makefile -f _RocqProject -o RocqMakefile`

Then, to compile/check all proof scripts listed in `_RocqProject_`:

`make -f RocqMakefile all`

To remove generated files, run:

`make -f RocqMakfile cleanall`

Compatibility tested with Rocq `9.10.0`.

## Contents

- Target language : [stlc_target.v](stlc_target.v)
- Anontation-directed selective CPS-transform : [stlc_cont_annot.v](stlc_cont_annot.v)
- Fully type-directed selective CPS-transform : [stlc_cont_ty.v](stlc_cont_ty.v)