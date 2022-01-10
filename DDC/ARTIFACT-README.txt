Artifact submission for ESOP 2022 paper 111
==========================================

This artifact includes Coq proofs for the results claimed about DDC in 
in [the submitted
paper](https://github.com/sweirich/graded-haskell/blob/main/ddc.pdf)
accepted to ESOP 2022. 

Getting Started Guide
=====================

Download instructions
---------------------

The artifact is available as a [VirtualBox](https://www.virtualbox.org/) available for download from 

https://drive.google.com/file/d/1r7fiVdKiPF-cHD29mhkF9iWC-Mwj4ZyP/view?usp=sharing

After starting VirtualBox, the machine can be loaded via 

     File > Import Appliance...


Evaluation instructions
-----------------------

Note: reviwers can use the following credentials for administrator access on
the virtual machine.

     username: osboxes
     password: osboxes.org

To use Coq to verify the claims, reviewers should import the provided virtual box
file.

Then, to compile the development, perform the following commands in a terminal window.
  
     cd ~ 
     cd graded-haskell/DDC/src
     make clean
     make coq

NOTE: On 2019 MacBook Pro, the entire development takes < 4 minutes to
compile. 

A successful compilation should produce the following output.

```
{ echo "-R . Qual " ; ls *.v ; } > _CoqProject && coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o CoqSrc.mk
make[1]: Entering directory '/Users/sweirich/github/coq/graded-haskell/DDC/src'
COQC grade_sig.v
COQC sort_sig.v
COQC Qualitative_ott.v
COQC Qualitative_inf.v
COQC metalib.v
COQC tactics.v
COQC labels.v
COQC weakening.v
COQC uniq.v
COQC subst.v
COQC grade.v
COQC geq.v
COQC defeq.v
COQC par.v
COQC confluence.v
COQC consist.v
COQC narrowing.v
COQC pumping.v
COQC typing_ctx_fv.v
COQC typing.v
COQC erasure.v
COQC progress.v
COQC strong_exists.v
make[1]: Leaving directory '/Users/sweirich/github/coq/graded-haskell/DDC/src'
```

The source code for the artifact is available from the public github repository:
https://github.com/sweirich/graded-haskell/tree/main/DDC


Step-by-Step Instructions
=========================

Complete claims made by the paper substantiated by this artifact
----------------------------------------------------------------

This artifact substantiates the results claimed in the paper as indicated by
the footnotes. All results are proved about the DDC calculus, presented in
Section 5.  The language DDC^Top (Section 4) is an instance of DDC,
so these results hold directly for that language as well.

* System specification

The full specification of the type system shown in Section 5 is in the file
`Qualitative_ott.v`. This file has been mechanically generated from the Ott
specification `Qualitative.ott` and then patched. For convenience, we
also provide the file `spec.pdf` that contains a typeset version of the
system, also generated from `Qualitative.ott`.

Note: the DDC in the artifact includes *both* weak and strong sigma-types
as primitive type forms. The file `strong_exists.v` shows that the rules 
for projection from strong sigmas are derivable from weak sigmas. Therefore, 
the paper only includes the specification of weak sigmas.

* Key results

The individual results can be found in the corresponding Coq files and theorem
statements as directed by the paper's footnotes. (All Coq files are in the
`src` subdirectory.)

** Section 3

NOTE: the paper presents these lemmas about SDC, but our Coq proofs show that
they also hold for DDC. Reveiwers found this confusing, so in our revision of the
paper we will clarify.

     Lemma 5 (Typing implies grading)
     Lemma 6 (Equivalence) 
     Lemma 7 (Indistinguishability under substitution)
     Theorem 1 (Non-interference) 
      
** Section 5

      Theorem 8 (Consistency)
      Lemma 8 (Canonical Element)
      Lemma 9 (Erasure Indistinguishability)
      Lemma 10 (Erasure simulation)
      Lemma 11 (Narrowing)
      Lemma 12 (Weakening)
      Lemma 13 (Restricted Upgrading) 
      Lemma 14 (Bounded by C)
      Lemma 15 (Subsumption)
      Lemma 16 (Substitution)
      Lemma 17 (Regularity)
      Lemma 18 (Preservation)
      Lemma 19 (Progress)
      
** New material

The reviewers have requested more details about the decidability of type
checking for certain instances of DDC. In support of the new claims, we will
add the following theorem to the paper showing the equivalence of definitional
equality and the joins relation.  (The other direction of this lemma is
already used to show consistency.)

    Lemma Joins_DefEq : 
       forall S D A B, Joins S D A B -> DefEq S D A B.
       
This lemma appears at the end of the file src/consist.v.
      

* Parameters and Axioms made in Coq development

The DDC system is parameterized in two ways: first by a lattics of dependency
levels and then by the Sorts/Axioms/Rules as in a Pure Type system. These inputs
are marked as parameters.

- Abstract properties of the lattice (grade_sig.v)
- Sorts, Axioms and Rules of the Pure Type System (sort_sig.v) as described at 
  the beginning of Section 5.
  
The proof stated in the paper rely on minor axioms:

- Two properties about variable renaming (strong_exists.v)
- Lemmas about substitution generated by LNgen tool (Qualitative_inf.v)

For the latter, a version of the file that includes the full proofs of these
lemmas is also available (Qualitative_inf.full). This file takes a few minutes
to compile. If the reviewers would like to verify these assumptions, they can 
update the contents of the file Qualitative_inf.v with that of Qualitative_inf.full.

Complete claims made by the paper NOT substantiated by this artifact
----------------------------------------------------------------

This artifact only includes results about the DDC language. Therefore, results
about SDC or about a translation between languages have not been proved in Coq. 
These include the following results:

* Section 3

Lemmas 1-7, Theorem 1.  Properties of SDC that are similar to analogous results for DDC.
Theorems 2-4. Translation between DCC and SDC.

* Section 4

Theorems 5-7. Translation between SDC and DDC^Top.

Additional artifact description
-------------------------------

See the [README.md](https://github.com/sweirich/graded-haskell/tree/main/DDC/README.md) for the artifact site.

Constructing the artifact from scratch
--------------------------------------

The following commands will install all dependencies for the development from
a fresh version of Ubuntu.

- sudo apt install git-all
- sudo add-apt-repository ppa:avsm/ppa
- sudo apt update
- sudo apt install make
- sudo apt install gcc
- sudo apt install opam
- opam init
- opam switch create 4.09.1
- eval $(opam env --switch=4.01.1)
- opam repo add coq-released https://coq.inria.fr/opam/released
- opam pin coq 8.10.2
- opam install ott
- opam pin add coq-metalib https://github.com/plclub/metalib.git
- git clone https://github.com/sweirich/graded-haskell.git
- cd graded-haskell/DDC/src
- make coq
