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

A [Virtual Box](https://www.cis.upenn.edu/~sweirich/popl2021-paper408.ova) containing the Coq proof
scripts is available.

[DDC](DDC/)
-----------

"A Dependent Dependency Calculus", paper by Pritam Choudhury, Harley Eades III, and Stephanie Weirich.  
To appear in ESOP 2022.

The paper is [available](DDC/esop2022-paper111.pdf).

The extended version of the paper, with the full appendix, is available from [arXiv](https://arxiv.org/abs/2201.11040).

This [repository](DDC/) proves type soundness for DDC, including the
consistency of a grade-indexed definitional equivalence.

A [Virtual Box](https://zenodo.org/record/5903727#.YfqZGvXMLUI) containing the Coq proof
scripts is available.
