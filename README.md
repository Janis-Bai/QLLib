# Towards a Library of Quantitative Logics in Rocq

This repository contains the Rocq code accompanying the Rocqshop 2026 submission by Janis Bailitis, Reynald Affeldt, Alessandro Bruni, Alessio Coltelacci, Ekaterina Komendantskaya, and Kathrin Stark titled "Towards a Library of Quantitative Logics in Rocq".

RocqDoc documentation can be found [here](https://janis-bai.github.io/QLLib/Rocqshop_2026/toc.html).

The mechanisation consists of the following files:
- `interval_einference.v`: Implementation of interval inference for inversion on extended reals and powers where the base is an extended real and the exponent a real.
- `nonneg_ereal.v`: Definition of p-sums, (co)multiplication, and inversion on nonnegative extended reals together with properties about them.
- `qll_core.v`: Definition of pQLL's calculus, and work in progress towards completeness of pQLL without propositional variables
- `qll_cut_elim.v`: Cut admissibility proof for the one-sided variant of pQLL. Soon to be extended to the two-sided variant.

## Compilation Instructions

The code has been tested on Rocq `9.1`, compiled with OCaml `4.14.2`. It requires [MathComp](https://github.com/math-comp/math-comp), [MathComp-analysis](https://github.com/math-comp/analysis), and [MathComp-finmap](https://github.com/math-comp/finmap).

Installing the following components via `opam` should be sufficient to compile the code:
```
rocq-hierarchy-builder
rocq-mathcomp-algebra
rocq-mathcomp-bigenough
rocq-mathcomp-boot
rocq-mathcomp-field
rocq-mathcomp-fingroup
rocq-mathcomp-finmap
rocq-mathcomp-order
rocq-mathcomp-solvable
rocq-mathcomp-ssreflect
coq-mathcomp-zify
```

To compile the code, clone the repository, install the dependencies listed above, and run `make all` to start the compilation.
