Graded Haskell
=============

This repository contains mechanizations for two dependently-typed languages
with graded types --- i.e. type systems where each variable in the context is
annotated by some label drawn from an algebraic structure.

[GraD](GraD/)
-------------

"A Graded Dependent Type System with a Usage-Aware Semantics", by Pritam
Choudhury, Harley Eades III, Richard A. Eisenberg and Stephanie Weirich.
Published in POPL 2021 and available 
[here](https://dl.acm.org/doi/10.1145/3434331)
(with a local copy [here](https://github.com/sweirich/graded-haskell/blob/main/popl21-choudhury.pdf)).

Pritam's [POPL 2021 video](https://www.youtube.com/watch?v=yrwtXrey7mE) about this work (30 minutes).

The extended version of the paper is available from [arXiv](https://arxiv.org/abs/2011.04070).

This [repository](GraD/src) proves type soundness for GraD, assuming the consistency of an
unspecified definitional equivalence.

[DDC](DDC/)
-----------

"A Dependent Dependency Calculus", draft paper by Pritam
Choudhury, Harley Eades III, and Stephanie Weirich.

The draft paper is [available](ddc.pdf).

This [repository](DDC/src) proves type soundness for DDC, including the
consistency of a grade-indexed definitional equivalence.
