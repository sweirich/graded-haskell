Artifact submission for POPL2021 paper 408
==========================================

This repository includes Coq proofs for the results claimed in Section 6.2
(Metatheory) of [this
paper](https://github.com/sweirich/graded-haskell/blob/main/submitted-version.pdf),
conditionally accepted to POPL 2021. 

Download, installation, and sanity-testing instructions
---------------------------------------------------------

The artifact is available as a [VirtualBox](https://www.virtualbox.org/) available for download from 

http://www.seas.upenn.edu/~sweirich/popl21-paper408.ova

After starting VirtualBox, the machine can be loaded via 

     File > Import Appliance...

The source code for the artifact is available from the public github repository:
https://github.com/sweirich/graded-haskell

Complete claims made by the paper substantiated by this artifact
----------------------------------------------------------------

This artifact substantiates the results claimed in Section 6.2 (Metatheory).
No other results of the paper have been mechanically checked.

For convenience, the [submitted version of the paper](https://github.com/sweirich/graded-haskell/blob/main/submitted-version.pdf) is available from the github repository.

* Key results

The individual results of this Section can be found in the corresponding Coq
files and theorem statements. (All Coq files are in the `src` subdirectory.)

      Lemma 6.1 (Regularity)      dqtt.v: Typing_regularity
      Lemma 6.2 (Substitution)    structural.v: substitution
      Lemma 6.3 (Weakening)       structural.v: weakening
      Theorem 6.4 (Preservation)  dqtt.v: preservation
      Theorem 6.5 (Progress)      dqtt.v: progress

* System specification

The full specification of the type system shown in Section 6.1 is in the file
`dqtt_ott.v`. This file has been mechanically generated from the Ott
specification `dqtt.ott`, but then slightly edited. For convenience, we also
provide the file `spec.pdf` that contains a typeset version of the system,
also generated from `dqtt.ott`.

* Assumptions made in Coq development

The axioms that our development relies on are in the files `usage_sig.v`
and `beta.v`.  The first file is an axiomatization of the partially-ordered
semi-ring structure, as described in Section 2.1 of the paper. The second file
describes the axiomatization of beta-equivalence as specified in Definition
7.1.

Evaluation instructions
-----------------------

To evaluate these claims, reviewers should import the provided virtual box
file.  Once the machine has been booted, a Terminal can be started
using the icon at the top-left of the screen.

Then, to compile the development, perform the following commands in a terminal window.
  
     cd ~ 
     cd graded-haskell/src
     make clean
     make coq

NOTE: to access the latest version of the artifact, reviewers may wish to do a `git pull` 
in the `graded-haskell` directory.

NOTE: On 2019 MacBook Pro, the entire development takes < 4 minutes to
compile. The file `dqtt_inf.v` (generated from LNgen) is the largest component
of that time.

Note: reviwers can use the following credentials for administrator access on
the virtual machine.

     username: sweirich
     password: popl2021


Additional artifact description
-------------------------------

See the [README.md](https://github.com/sweirich/graded-haskell) for the artifact site.
