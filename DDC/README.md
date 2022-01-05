The [src](src/) directory includes a Coq specification of a dependently typed
calculus with dependent functions, unit, products and sums.

System Specification 
--------------------

The full specification of the DDC type system is in the file
[Qualitative_ott.v](src/Qualitative_ott.v]. This file has been mechanically
generated from the Ott specification in [Qualitative.ott](Qualitative.ott),
but then slightly edited. For convenience, we also provide the file
[spec.pdf](spec.pdf) that contains a typeset version of the system, also
generated from the same specification file.

Compilation Instructions
-----------------------

This development has been tested with The Coq Proof Assistant, version 8.10.2 

To compile this code with Coq, you also need to install a copy of the Metalib
library. This library is available from https://github.com/plclub/metalib at
the coq8.10 tag.

You can install these tools via opam (https://opam.ocaml.org/): 

     opam switch create 4.09.1
     opam repo add coq-released https://coq.inria.fr/opam/released
     opam pin coq 8.10.2
     opam install ott
     opam pin add coq-metalib https://github.com/plclub/metalib.git

Once Coq and metalib have been installed, the files can be compiled using

      cd src; make coq


Contents
--------

* System specification and utilities

      grade_sig.v            - Abstract lattice of grades
      sort_sig.v             - Abstract sorts, axioms, rules for PTS

      Qualitative_ott.v      - Generated from Ott, using typing.patch
      Qualitative_inf.v      - Generated from LNgen (axiomatized)
      Qualitative_inf_full.v - Generated from LNgen (full proofs)
      metalib.v              - Potential additions to LNgen
      tactics.v              - general proof machinery
      labels.v               - Properties of context functions

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
                                 respects step  (Main non-interference theorem)
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

* Other

      strong_exists.v      - Derive projections of strong Sigmas from pattern matching
                             [Caveat: two Axioms about variable renaming.]
      erasure.v            - Justify using runtime irrelevance to erase terms




