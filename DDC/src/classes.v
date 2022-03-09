Require Import Metalib.Metatheory.
Require Import Metalib.LibLNgen.

Create HintDb syntax.
Create HintDb fv.
Create HintDb open.
Create HintDb close.
Create HintDb size.
Create HintDb subst.
Create HintDb lc.

(***********************************************************************)
(** * Operations *)
(***********************************************************************)

(* operations with a single type *)

Class Syntax (e :  Set) := {
    fv : e -> vars ;
    lc : e -> Prop;
    close_rec : nat -> atom -> e -> e ;
    size : e -> nat;
}.

Definition close {e} `{ Syntax e} := close_rec 0.

(* operations with multiple types *)

Class Subst (e : Set) (u : Set) `{Syntax e} `{Syntax u} := {
    open_rec  : nat -> u -> e -> e ;
    subst : u -> atom -> e -> e    
}.

Definition open {e}{u} `{Subst e u}  (e0 : e) (u0 : u) := open_rec 0 u0 e0.

(***********************************************************************)
(** * Theory *)
(***********************************************************************)

(* These are the general form of the lemmas in the Lemmas.v file; and 
   perhaps automatically proven by a future version of LNgen. *)
   

Class SyntaxTheory (exp : Set) `{H: Syntax exp} := {

    fv_close : forall a1 x1,
      fv (close x1 a1) [=] remove x1 (fv a1);
    
    close_inj : forall (e1 : exp) e2 x1,
      close x1 e1 = close x1 e2 ->
      e1 = e2;
   }.


Class SubstOpenTheory (exp : Set) (u : Set) (uvar : atom -> u) `{H: Subst exp u} 
      `{HU: Subst u u} := {
    
    subst_open : forall (a3 : exp) (a1 : u) (a2 : u) x1,
      lc a1 -> 
      subst a1 x1 (open a3 a2) = open (subst a1 x1 a3) (subst a1 x1 a2);
  }.

Class SubstTheory (exp : Set) (u : Set) (uvar : atom -> u) `{H: Subst exp u} := {
    
    fv_open_lower : forall a1 a2,
      fv a1 [<=] fv (open a1 a2);
    
    fv_open_upper : forall a1 a2,
      fv (open a1 a2) [<=] fv a2 `union` fv a1;
    
    open_close : forall (e1 : exp) x1,
      open (close x1 e1) (uvar x1) = e1;

    size_open_var : forall a x, 
      size (open a (uvar x)) = size a;
    
    open_inj : forall (e2 e1:exp) x1,
      x1 `notin` fv e2 ->
      x1 `notin` fv e1 ->
      open e2 (uvar x1) = open e1 (uvar x1) ->
      e2 = e1;

    subst_intro  : forall (x1:atom) (e1 : exp) (e2 : u),
      x1 `notin` fv e1 ->
      open e1 e2  = subst e2 x1 (open e1 (uvar x1)) ;
    
    subst_open_var : forall (e2 : exp) e1 x1 x2,
      x1 <> x2 ->
      lc e1 ->
      open (subst e1 x1 e2) (uvar x2) = 
        subst e1 x1 (open e2 (uvar x2));
    
    subst_fresh_eq : forall a2 a1 x1,
      x1 `notin` fv a2 ->
      subst a1 x1 a2 = a2;
        
    subst_lc : forall a1 a2 x1,
      lc a1 ->
      lc a2 ->
      lc (subst a2 x1 a1);
    
    subst_spec: forall a1 a2 x1, 
      subst a2 x1 a1 = open (close x1 a1) a2;
                                        
    subst_close : forall a2 a1 x1 x2,
      lc a1 ->  x1 <> x2 ->
      x2 `notin` fv a1 ->
      subst a1 x1 (close x2 a2) = close x2 (subst a1 x1 a2);

  (* still not included 
     
  fv_subst_fresh := fv_exp_subst_exp_wrt_exp_fresh;
  fv_subst_lower := fv_exp_subst_exp_wrt_exp_lower;
  fv_subst_notin := fv_exp_subst_exp_wrt_exp_notin;
  fv_subst_upper := fv_exp_subst_exp_wrt_exp_upper;
  *)

  }.


#[export] Hint Rewrite @subst_open
  using solve [auto; try typeclasses eauto] : syntax.

#[export] Hint Rewrite @subst_close
  using solve [auto; try typeclasses eauto] : syntax.

#[export] Hint Rewrite @open_close
  using solve [auto; try typeclasses eauto] : syntax.

#[export] Hint Rewrite @size_open_var
  using solve [auto; try typeclasses eauto] : syntax.

#[export] Hint Resolve subst_lc : lc.

(***********************************************************************)
(** * Rewriting / tactics *)
(***********************************************************************)


Ltac simp_syntax := repeat first [ 
                       autorewrite with subst
                     || autorewrite with open
                     || autorewrite with close
                     || autorewrite with fv
                     || autorewrite with size
                     || autorewrite with syntax
                     ].

Ltac simp_syntax_in H := repeat first [ 
                       autorewrite with subst in H
                     || autorewrite with open in H
                     || autorewrite with close in H
                     || autorewrite with fv in H 
                     || autorewrite with size in H
                     || autorewrite with syntax in H
                     ].


Lemma lc_body
     : forall {A1 A2:Set} {a1 : A1}{a2 : A2}{v} `{SubstTheory A1 A2 v}, 
    (forall x, lc (open a1 (v x))) -> lc a2 -> lc (open a1 a2).
Proof.
  intros.
  pick fresh x for (fv a1). 
  rewrite (subst_intro x); auto.
  apply subst_lc; eauto.
Qed.

#[export] Hint Resolve lc_body : lc.


(***********************************************************************)
(** * Notations *)
(***********************************************************************)

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [e ^ x] can be read as "substitute the variable [x]
    for index [0] in [e]".
*)

Declare Scope syntax_scope.
Module SyntaxNotations.
Notation "[ z ~> u ] e" := (subst u z e) (at level 0) : syntax_scope.
Notation "e ^ x"        := (open x e) : syntax_scope.
End SyntaxNotations.

