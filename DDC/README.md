Overview 
--------

* System Specification 

The full specification of the type system shown in Section 7.1 is in the file
Qualitative_ott.v. This file has been mechanically generated from the Ott
specification, but then slightly edited. For convenience, we also provide the
file spec.pdf that contains a typeset version of the system, also generated
from the same specification file.

* Assumptions

We axiomatize a few parts:
  - lemmas about substitution generated by LNgen tool (Qualitative_inf.v)
  - local closure properties of all relations (see tactics.v)
  - abstract properties of the lattice (grade_sig.v)
    

Compilation Instructions
-----------------------

Installation and Compilation Instructions
This development has been tested with The Coq Proof Assistant, version 8.10.2 

To compile this code with Coq, you also need to install a copy of the Metalib library. This library is available from https://github.com/plclub/metalib at the coq8.10 tag.

This directory includes a Coq specification of a dependently typed calculus with type-in-type, dependent functions, unit, products and sums.

Once Coq and metalib have been installed, the files can be compiled using

      make coq

You may also be able to install via OPAM:

     opam switch create ./ OCAML_VERSION
     opam repo add coq-released https://coq.inria.fr/opam/released
     opam install coq coq-ott ott
     opam pin add coq-metalib https://github.com/plclub/metalib.git


Contents
--------

grade_sig.v          - Abstract lattice of grades

Qualitative_ott.v    - Generated from Ott, using typing.patch
Qualitative_inf.v    - Generated from LNgen
metalib.v            - Potential additions to LNgen
tactics.v
labels.v             - Properties of context functions

* Structural lemmas 

uniq.v               - Judgements use uniq contexts
narrowing.v          - Narrowing lemmas
weakening.v          - Weakening lemmas
pumping.v            - Can raise context vars up to level of judgment
subst.v              - Substitution lemmas for Grade/GEq/DefEq/Par

* Judgement specific lemmas

grade.v              - Step relation preserves Grade
geq.v                - Properties of CEq / GEq 
                           equivalence relation
                           respects step
                           implies Grade
defeq.v              - Properties of DefEq
                           implies grade
                           contains GEq
                           additional substitution lemmas

* Preservation

typing_ctx_fv.v      - Free variables are in domain of typing judgement
typing.v             - Main Preservation lemma

* Progress

par.v                - Properaties of Par relation
confluence.v         - Parallel reduction is confluent
consist.v            - Definitional Equality is consistent
progress.v           - Main Progress lemma

strong_exists.v      - Derive projections of strong Sigmas from weak Sigmas

=============================================================


