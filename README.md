# Towards a Library of Quantitative Logics in Rocq

This repository contains the Rocq code accompanying the Rocqshop 2026 submission by Janis Bailitis, Reynald Affeldt, Alessandro Bruni, Alessio Coltellacci, Ekaterina Komendantskaya, and Kathrin Stark titled "Towards Quantitative Logics in Rocq".

RocqDoc documentation can be found [here](https://janis-bai.github.io/QLLib/Rocqshop_2026/toc.html).

The mechanisation consists of the following files:
- `interval_einference.v`: Implementation of interval inference for inversion on extended reals and powers where the base is an extended real and the exponent a real.
- `nonneg_ereal.v`: Definition of p-sums, (co)multiplication, and inversion on nonnegative extended reals together with properties about them.
- `qll_core.v`: Definition of pQLL's calculus, and work in progress towards completeness of pQLL without propositional variables
- `qll_theories.v`: Constructions of pQLL theories (sets of axioms `r ≤ Γ ⊢ Δ` bounding the validity of sequents from below, defined in `qll_defs.v`, which parameterises the two-sided calculus by a theory): grounded theories induced by a valuation of the propositional constants, Bayesian theories over a finite outcome space, and an example derivation `A ⊢ A ∩ B` between events
- `qll_rat_validity.v`: A computable rational mirror of the validity of one-sided proofs, which coincides with the real-valued validity when the additive annotation is 1; it makes comparisons of validities decidable.
- `qll_cut_elim.v`: Cut admissibility proof for the one-sided variant of pQLL, stated in `Type` so the rewritten cut-free proof is an extractable term (`cut_eliminate`). The semantic choices of the procedure are abstracted into an oracle; with the rational oracle (annotation 1), the choices are decided by computation. The whole proof chain is transparent (`Defined`, no Qed-opaque transports or `ssr_have` on the witness path), so on closed derivations the extracted cut-free proof normalises inside Rocq by `vm_compute` (see the `computation_tests` section for examples, including the full two-sided pipeline).

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
