Artifact submission for POPL2021 paper 408
==========================================

Complete claims made by the paper substantiated by this artifact
----------------------------------------------------------------

This artifact substantiates the results claimed in Section 6.2 (Metatheory).

* Key results

The individual results can be found in the corresponding Coq files and theorem 
statements.

      Lemma 6.1 (Regularity)      dqtt.v: Typing_regularity
      Lemma 6.2 (Substitution)    structural.v: substitution
      Lemma 6.3 (Weakening)       structural.v: weakening
      Theorem 6.4 (Preservation)  dqtt.v: preservation
      Theorem 6.5 (Progress)      dqtt.v: progress  

* System specification

The full specification of the type system shown in Section 6.1 is in the file
`dqtt_ott.v`. This file has been generated from the Ott specification `dqtt.ott`,
but then slightly edited, as described below. For convenience, we also provide
the file `spec.pdf` that contains a typeset version of the system, also
generated from `dqtt.ott`.

* Assumptions made in Coq development

The axioms that our development relies on are in the files `usage_sig.v`
and `beta.v`.  The first file is an axiomatization of the partially-ordered
semi-ring structure, as described in Section 2.1 of the paper. The second file
describes the axiomatization of beta-equivalence as specified in Definition
7.1.

Download, installation, and sanity-testing instructions
---------------------------------------------------------

The artifact is available as a virtual box available for download from ...

The source code for the artifact is available from the public github repository:
https://github.com/sweirich/graded-haskell

Evaluation instructions
-----------------------

To evaluate these claims, reviewers should log into the provided virtual box
with the following credentials:

     username: sweirich
     password: popl2021

Then perform the following commands in a terminal window.
  
     cd ~ 
     cd graded-haskell/src
     make clean
     make coq

NOTE: to access the latest version of the artifact, reviewers may wish to do a `git pull` 
in the `graded-haskell` directory.

NOTE: On 2019 MacBook Pro, the entire development takes < 4 minutes to compile. The file `dqtt_inf.v` (generated from LNgen) is the largest component of that time. 
     

Additional artifact description
-------------------------------

This development has been tested with The Coq Proof Assistant, version 8.11.1
(May 2020).

To compile this code with Coq, you also need to install a copy of the Metalib
library.  This library is available from https://github.com/plclub/metalib

The `src/` directory includes a Coq specification of a dependently typed
calculus with type-in-type, dependent functions, unit, products and sums.

The files that make up the Coq development include:

- dqtt.ott     Specification of the entire system
- dqtt_ott.v   Generated definition (from Ott, modified by hand)
- dqtt_inf.v   Generated lemmas (from LNgen). 
- tactics.v    General purpose tactics
- metalib.v    metalib additions

- beta.v       Axiomatization of beta-equivalence
- usage_sig.v  Axiomatization of partially-ordered semiring

- usage.v      Lemmas about working with usages and with graded contexts (language independent)
- dctx.v     
- dctx_sub. v 
- semimodule.v

- structural.v  Substitution and Weakening (Lemmas 6.2 and 6.3)
- dqtt.v        Regularity, Preservation and Progress (Lemma 6.1, Theorems 6.4 and 6.5)


