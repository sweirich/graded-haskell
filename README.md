A Graded Dependent Type System
==============================

"A graded dependent type system with a usage-aware semantics", by
Pritam Choudhury, Harley Eades III, Richard A. Eisenberg and Stephanie Weirich will appear in POPL 2021 and a preprint is available [here](https://github.com/sweirich/graded-haskell/blob/main/popl21-choudhury.pdf).

The extended version of the paper is available from [arXiv](https://arxiv.org/abs/2011.04070).

* Key results

This repository includes Coq proofs for the results claimed in Section 7.2 of the 
paper.

The individual results can be found in the corresponding Coq files and theorem
statements. (All Coq files are in the `src` subdirectory.)

      Lemma 7.1 (Regularity)      dqtt.v: Typing_regularity
      Lemma 7.2 (Substitution)    structural.v: substitution
      Lemma 7.3 (Weakening)       structural.v: weakening
      Theorem 7.4 (Preservation)  dqtt.v: preservation
      Theorem 7.5 (Progress)      dqtt.v: progress

* System specification

The full specification of the type system shown in Section 7.1 is in the file
`dqtt_ott.v`. This file has been mechanically generated from the Ott
specification `dqtt.ott`, but then slightly edited. For convenience, we also
provide the file
[spec.pdf](https://github.com/sweirich/graded-haskell/blob/main/spec.pdf) that
contains a typeset version of the system, also generated from `dqtt.ott`.

* Assumptions 

The axioms that our development relies on are in the files `usage_sig.v`
and `beta.v`.  The first file is an axiomatization of the partially-ordered
semi-ring structure, as described in Section 2.1 of the paper. The second file
describes the axiomatization of beta-equivalence as specified in Definition
9.1.

* Version with definitions

The directory `src-def` extends the system with definitions in the context as described in Section 8.1 of the paper and reproves Lemmas 7.1--7.5. It does not include any of the new results of that section (Lemmas 8.1--8.4).

Installation and Compilation Instructions
------------------------------------------

This development has been tested with The Coq Proof Assistant, version 8.11.1
(May 2020).

To compile this code with Coq, you also need to install a copy of the Metalib
library.  This library is available from https://github.com/plclub/metalib
at the `coq8.10` tag.

The `src/` directory includes a Coq specification of a dependently typed
calculus with type-in-type, dependent functions, unit, products and sums.

Once Coq and metalib have been installed, the files in the `src/` directory 
can be compiled using 

    make coq
    
You may also be able to install via OPAM:

    opam switch create ./ OCAML_VERSION
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq coq-ott ott
    opam pin add coq-metalib https://github.com/plclub/metalib.git

Contents
--------

The files that make up the Coq development include:

    - dqtt.ott     Specification of the entire system
    - dqtt_ott.v   Generated definition (from Ott, modified by hand)
    - dqtt_inf.v   Generated lemmas (from LNgen, modified by hand). 
    - tactics.v    General purpose tactics
    - metalib.v    metalib additions

    - beta.v       Axiomatization of beta-equivalence
    - usage_sig.v  Axiomatization of partially-ordered semiring

    - usage.v      Lemmas about working with usages and with graded contexts (language independent)
    - dctx.v     
    - dctx_sub. v 
    - semimodule.v

    - structural.v  Substitution and Weakening (Lemmas 7.2 and 7.3)
    - dqtt.v        Regularity, Preservation and Progress (Lemma 7.1, Theorems 7.4 and 7.5)


Binding Representation
----------------------
This proof uses a Locally Nameless representation for binding, as supported by the [Ott locallynameless backend](https://fzn.fr/projects/ln_ott/) and [LNgen](https://repository.upenn.edu/cis_reports/933/) tools.

For background on this binding representation, please see: 
* [Engineering Formal Metatheory](https://repository.upenn.edu/cis_papers/369/)
* [DeepSpec Summer School 2017 Tutorial on Locally Nameless Representation](https://deepspec.org/event/dsss17/lecture_weirich.html) 
