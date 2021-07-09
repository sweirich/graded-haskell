System with Definitions
----------------------

This directory proves substitutions, weakening, regularity, preservation and progress for the system extended with definitions, as described in Section 8.1 of the POPL 2021 paper.

This code is an extension of the language shown in the `src/` directory. It
has not been evaluated by the POPL 2021 artifact evaluation committee.

To compile this code with Coq, you also need to install a copy of the Metalib
library.  This library is available from https://github.com/plclub/metalib

This is Coq specification of a dependently typed calculus with type-in-type,
dependent functions, unit, products and sums.

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

- structural.v  Substitution and Weakening 
- dqtt.v        Regularity, Preservation and Progress 


