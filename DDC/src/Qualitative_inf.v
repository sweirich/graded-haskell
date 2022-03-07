Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export Qualitative_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme tm_ind' := Induction for tm Sort Prop.

Definition tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 =>
  tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.

Scheme tm_rec' := Induction for tm Sort Set.

Definition tm_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 =>
  tm_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.


(* *********************************************************************** *)
(** * Close *)

(*
Fixpoint close_tm_wrt_tm_rec (n1 : nat) (x1 : tmvar) (a1 : tm) {struct a1} : tm :=
  match a1 with
    | a_TyUnit => a_TyUnit
    | a_TmUnit => a_TmUnit
    | a_Pi psi1 A1 B1 => a_Pi psi1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_Abs psi1 A1 a2 => a_Abs psi1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 a2)
    | a_App a2 psi1 b1 => a_App (close_tm_wrt_tm_rec n1 x1 a2) psi1 (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Type s1 => a_Type s1
    | a_Var_f x2 => if (x1 == x2) then (a_Var_b n1) else (a_Var_f x2)
    | a_Var_b n2 => if (lt_ge_dec n2 n1) then (a_Var_b n2) else (a_Var_b (S n2))
    | a_Sum A1 A2 => a_Sum (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec n1 x1 A2)
    | a_Inj1 a2 => a_Inj1 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Inj2 a2 => a_Inj2 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Case psi1 a2 b1 b2 => a_Case psi1 (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1) (close_tm_wrt_tm_rec n1 x1 b2)
    | a_WSigma psi1 A1 B1 => a_WSigma psi1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_WPair a2 psi1 b1 => a_WPair (close_tm_wrt_tm_rec n1 x1 a2) psi1 (close_tm_wrt_tm_rec n1 x1 b1)
    | a_LetPair psi1 a2 b1 => a_LetPair psi1 (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec (S n1) x1 b1)
    | a_SSigma psi1 A1 B1 => a_SSigma psi1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_SPair a2 psi1 b1 => a_SPair (close_tm_wrt_tm_rec n1 x1 a2) psi1 (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Proj1 psi1 a2 => a_Proj1 psi1 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Proj2 psi1 a2 => a_Proj2 psi1 (close_tm_wrt_tm_rec n1 x1 a2)
  end.

Definition close_tm_wrt_tm x1 a1 := close_tm_wrt_tm_rec 0 x1 a1.
*)

(* *********************************************************************** *)
(** * Size *)

(*
Fixpoint size_tm (a1 : tm) {struct a1} : nat :=
  match a1 with
    | a_TyUnit => 1
    | a_TmUnit => 1
    | a_Pi psi1 A1 B1 => 1 + (size_grade psi1) + (size_tm A1) + (size_tm B1)
    | a_Abs psi1 A1 a2 => 1 + (size_grade psi1) + (size_tm A1) + (size_tm a2)
    | a_App a2 psi1 b1 => 1 + (size_tm a2) + (size_grade psi1) + (size_tm b1)
    | a_Type s1 => 1 + (size_sort s1)
    | a_Var_f x1 => 1
    | a_Var_b n1 => 1
    | a_Sum A1 A2 => 1 + (size_tm A1) + (size_tm A2)
    | a_Inj1 a2 => 1 + (size_tm a2)
    | a_Inj2 a2 => 1 + (size_tm a2)
    | a_Case psi1 a2 b1 b2 => 1 + (size_grade psi1) + (size_tm a2) + (size_tm b1) + (size_tm b2)
    | a_WSigma psi1 A1 B1 => 1 + (size_grade psi1) + (size_tm A1) + (size_tm B1)
    | a_WPair a2 psi1 b1 => 1 + (size_tm a2) + (size_grade psi1) + (size_tm b1)
    | a_LetPair psi1 a2 b1 => 1 + (size_grade psi1) + (size_tm a2) + (size_tm b1)
    | a_SSigma psi1 A1 B1 => 1 + (size_grade psi1) + (size_tm A1) + (size_tm B1)
    | a_SPair a2 psi1 b1 => 1 + (size_tm a2) + (size_grade psi1) + (size_tm b1)
    | a_Proj1 psi1 a2 => 1 + (size_grade psi1) + (size_tm a2)
    | a_Proj2 psi1 a2 => 1 + (size_grade psi1) + (size_tm a2)
  end.
*)

(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_tm_wrt_tm : nat -> tm -> Prop :=
  | degree_wrt_tm_a_TyUnit : forall n1,
    degree_tm_wrt_tm n1 (a_TyUnit)
  | degree_wrt_tm_a_TmUnit : forall n1,
    degree_tm_wrt_tm n1 (a_TmUnit)
  | degree_wrt_tm_a_Pi : forall n1 psi1 A1 B1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) B1 ->
    degree_tm_wrt_tm n1 (a_Pi psi1 A1 B1)
  | degree_wrt_tm_a_Abs : forall n1 psi1 A1 a1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) a1 ->
    degree_tm_wrt_tm n1 (a_Abs psi1 A1 a1)
  | degree_wrt_tm_a_App : forall n1 a1 psi1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_App a1 psi1 b1)
  | degree_wrt_tm_a_Type : forall n1 s1,
    degree_tm_wrt_tm n1 (a_Type s1)
  | degree_wrt_tm_a_Var_f : forall n1 x1,
    degree_tm_wrt_tm n1 (a_Var_f x1)
  | degree_wrt_tm_a_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_tm_wrt_tm n1 (a_Var_b n2)
  | degree_wrt_tm_a_Sum : forall n1 A1 A2,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm n1 A2 ->
    degree_tm_wrt_tm n1 (a_Sum A1 A2)
  | degree_wrt_tm_a_Inj1 : forall n1 a1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 (a_Inj1 a1)
  | degree_wrt_tm_a_Inj2 : forall n1 a1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 (a_Inj2 a1)
  | degree_wrt_tm_a_Case : forall n1 psi1 a1 b1 b2,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 b2 ->
    degree_tm_wrt_tm n1 (a_Case psi1 a1 b1 b2)
  | degree_wrt_tm_a_WSigma : forall n1 psi1 A1 B1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) B1 ->
    degree_tm_wrt_tm n1 (a_WSigma psi1 A1 B1)
  | degree_wrt_tm_a_WPair : forall n1 a1 psi1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_WPair a1 psi1 b1)
  | degree_wrt_tm_a_LetPair : forall n1 psi1 a1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm (S n1) b1 ->
    degree_tm_wrt_tm n1 (a_LetPair psi1 a1 b1)
  | degree_wrt_tm_a_SSigma : forall n1 psi1 A1 B1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) B1 ->
    degree_tm_wrt_tm n1 (a_SSigma psi1 A1 B1)
  | degree_wrt_tm_a_SPair : forall n1 a1 psi1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_SPair a1 psi1 b1)
  | degree_wrt_tm_a_Proj1 : forall n1 psi1 a1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 (a_Proj1 psi1 a1)
  | degree_wrt_tm_a_Proj2 : forall n1 psi1 a1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 (a_Proj2 psi1 a1).

Scheme degree_tm_wrt_tm_ind' := Induction for degree_tm_wrt_tm Sort Prop.

Definition degree_tm_wrt_tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 =>
  degree_tm_wrt_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.

#[export]
Hint Constructors degree_tm_wrt_tm : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_tm : tm -> Set :=
  | lc_set_a_TyUnit :
    lc_set_tm (a_TyUnit)
  | lc_set_a_TmUnit :
    lc_set_tm (a_TmUnit)
  | lc_set_a_Pi : forall psi1 A1 B1,
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm B1 (a_Var_f x1))) ->
    lc_set_tm (a_Pi psi1 A1 B1)
  | lc_set_a_Abs : forall psi1 A1 a1,
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm a1 (a_Var_f x1))) ->
    lc_set_tm (a_Abs psi1 A1 a1)
  | lc_set_a_App : forall a1 psi1 b1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm (a_App a1 psi1 b1)
  | lc_set_a_Type : forall s1,
    lc_set_tm (a_Type s1)
  | lc_set_a_Var_f : forall x1,
    lc_set_tm (a_Var_f x1)
  | lc_set_a_Sum : forall A1 A2,
    lc_set_tm A1 ->
    lc_set_tm A2 ->
    lc_set_tm (a_Sum A1 A2)
  | lc_set_a_Inj1 : forall a1,
    lc_set_tm a1 ->
    lc_set_tm (a_Inj1 a1)
  | lc_set_a_Inj2 : forall a1,
    lc_set_tm a1 ->
    lc_set_tm (a_Inj2 a1)
  | lc_set_a_Case : forall psi1 a1 b1 b2,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm b2 ->
    lc_set_tm (a_Case psi1 a1 b1 b2)
  | lc_set_a_WSigma : forall psi1 A1 B1,
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm B1 (a_Var_f x1))) ->
    lc_set_tm (a_WSigma psi1 A1 B1)
  | lc_set_a_WPair : forall a1 psi1 b1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm (a_WPair a1 psi1 b1)
  | lc_set_a_LetPair : forall psi1 a1 b1,
    lc_set_tm a1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm b1 (a_Var_f x1))) ->
    lc_set_tm (a_LetPair psi1 a1 b1)
  | lc_set_a_SSigma : forall psi1 A1 B1,
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm B1 (a_Var_f x1))) ->
    lc_set_tm (a_SSigma psi1 A1 B1)
  | lc_set_a_SPair : forall a1 psi1 b1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm (a_SPair a1 psi1 b1)
  | lc_set_a_Proj1 : forall psi1 a1,
    lc_set_tm a1 ->
    lc_set_tm (a_Proj1 psi1 a1)
  | lc_set_a_Proj2 : forall psi1 a1,
    lc_set_tm a1 ->
    lc_set_tm (a_Proj2 psi1 a1).

Scheme lc_tm_ind' := Induction for lc_tm Sort Prop.

Definition lc_tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 =>
  lc_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.

Scheme lc_set_tm_ind' := Induction for lc_set_tm Sort Prop.

Definition lc_set_tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 =>
  lc_set_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.

Scheme lc_set_tm_rec' := Induction for lc_set_tm Sort Set.

Definition lc_set_tm_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 =>
  lc_set_tm_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.

#[export] Hint Constructors lc_tm : core lngen.

#[export] Hint Constructors lc_set_tm : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_tm_wrt_tm a1 := forall x1, lc_tm (open_tm_wrt_tm a1 (a_Var_f x1)).

#[export] Hint Unfold body_tm_wrt_tm : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[export] Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_sort_min_mutual :
(forall s1, 1 <= size_sort s1).
Proof. Admitted.

(* end hide *)

Lemma size_sort_min :
forall s1, 1 <= size_sort s1.
Proof. Admitted.

#[export] Hint Resolve size_sort_min : lngen.

(* begin hide *)

Lemma size_grade_min_mutual :
(forall psi1, 1 <= size_grade psi1).
Proof. Admitted.

(* end hide *)

Lemma size_grade_min :
forall psi1, 1 <= size_grade psi1.
Proof. Admitted.

#[export] Hint Resolve size_grade_min : lngen.

(* begin hide *)

Lemma size_tm_min_mutual :
(forall a1, 1 <= size_tm a1).
Proof. Admitted.

(* end hide *)

Lemma size_tm_min :
forall a1, 1 <= size_tm a1.
Proof. Admitted.

#[export] Hint Resolve size_tm_min : lngen.

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 a1) = size_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  size_tm (close_tm_wrt_tm_rec n1 x1 a1) = size_tm a1.
Proof. Admitted.

#[export] Hint Resolve size_tm_close_tm_wrt_tm_rec : lngen.
Hint Rewrite size_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_tm_close_tm_wrt_tm :
forall a1 x1,
  size_tm (close_tm_wrt_tm x1 a1) = size_tm a1.
Proof. Admitted.

#[export] Hint Resolve size_tm_close_tm_wrt_tm : lngen.
Hint Rewrite size_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_mutual :
(forall a1 a2 n1,
  size_tm a1 <= size_tm (open_tm_wrt_tm_rec n1 a2 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec :
forall a1 a2 n1,
  size_tm a1 <= size_tm (open_tm_wrt_tm_rec n1 a2 a1).
Proof. Admitted.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma size_tm_open_tm_wrt_tm :
forall a1 a2,
  size_tm a1 <= size_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

#[export] Hint Resolve size_tm_open_tm_wrt_tm : lngen.

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var_mutual :
(forall a1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1) = size_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_tm_rec_var :
forall a1 x1 n1,
  size_tm (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1) = size_tm a1.
Proof. Admitted.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_rec_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_tm_open_tm_wrt_tm_var :
forall a1 x1,
  size_tm (open_tm_wrt_tm a1 (a_Var_f x1)) = size_tm a1.
Proof. Admitted.

#[export] Hint Resolve size_tm_open_tm_wrt_tm_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_tm_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_tm_wrt_tm_S_mutual :
(forall n1 a1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm (S n1) a1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_tm_S :
forall n1 a1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm (S n1) a1.
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_S : lngen.

Lemma degree_tm_wrt_tm_O :
forall n1 a1,
  degree_tm_wrt_tm O a1 ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_O : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 a1).
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm :
forall a1 x1,
  degree_tm_wrt_tm 0 a1 ->
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 a1).
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv_mutual :
(forall a1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 a1) ->
  degree_tm_wrt_tm n1 a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv :
forall a1 x1 n1,
  degree_tm_wrt_tm (S n1) (close_tm_wrt_tm_rec n1 x1 a1) ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_inv :
forall a1 x1,
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 a1) ->
  degree_tm_wrt_tm 0 a1.
Proof. Admitted.

#[export] Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_inv : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_mutual :
(forall a1 a2 n1,
  degree_tm_wrt_tm (S n1) a1 ->
  degree_tm_wrt_tm n1 a2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 a2 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec :
forall a1 a2 n1,
  degree_tm_wrt_tm (S n1) a1 ->
  degree_tm_wrt_tm n1 a2 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 a2 a1).
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm :
forall a1 a2,
  degree_tm_wrt_tm 1 a1 ->
  degree_tm_wrt_tm 0 a2 ->
  degree_tm_wrt_tm 0 (open_tm_wrt_tm a1 a2).
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm : lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv_mutual :
(forall a1 a2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 a2 a1) ->
  degree_tm_wrt_tm (S n1) a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv :
forall a1 a2 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_tm_rec n1 a2 a1) ->
  degree_tm_wrt_tm (S n1) a1.
Proof. Admitted.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_inv :
forall a1 a2,
  degree_tm_wrt_tm 0 (open_tm_wrt_tm a1 a2) ->
  degree_tm_wrt_tm 1 a1.
Proof. Admitted.

#[export] Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj_mutual :
(forall a1 a2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 a1 = close_tm_wrt_tm_rec n1 x1 a2 ->
  a1 = a2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_inj :
forall a1 a2 x1 n1,
  close_tm_wrt_tm_rec n1 x1 a1 = close_tm_wrt_tm_rec n1 x1 a2 ->
  a1 = a2.
Proof. Admitted.

#[export] Hint Immediate close_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_inj :
forall a1 a2 x1,
  close_tm_wrt_tm x1 a1 = close_tm_wrt_tm x1 a2 ->
  a1 = a2.
Proof. Admitted.

#[export] Hint Immediate close_tm_wrt_tm_inj : lngen.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  x1 `notin` fv_tm_tm a1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1) = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall a1 x1 n1,
  x1 `notin` fv_tm_tm a1 ->
  close_tm_wrt_tm_rec n1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1) = a1.
Proof. Admitted.

#[export] Hint Resolve close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.
Hint Rewrite close_tm_wrt_tm_rec_open_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_open_tm_wrt_tm :
forall a1 x1,
  x1 `notin` fv_tm_tm a1 ->
  close_tm_wrt_tm x1 (open_tm_wrt_tm a1 (a_Var_f x1)) = a1.
Proof. Admitted.

#[export] Hint Resolve close_tm_wrt_tm_open_tm_wrt_tm : lngen.
Hint Rewrite close_tm_wrt_tm_open_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  open_tm_wrt_tm_rec n1 (a_Var_f x1) (close_tm_wrt_tm_rec n1 x1 a1) = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  open_tm_wrt_tm_rec n1 (a_Var_f x1) (close_tm_wrt_tm_rec n1 x1 a1) = a1.
Proof. Admitted.

#[export] Hint Resolve open_tm_wrt_tm_rec_close_tm_wrt_tm_rec : lngen.
Hint Rewrite open_tm_wrt_tm_rec_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_close_tm_wrt_tm :
forall a1 x1,
  open_tm_wrt_tm (close_tm_wrt_tm x1 a1) (a_Var_f x1) = a1.
Proof. Admitted.

#[export] Hint Resolve open_tm_wrt_tm_close_tm_wrt_tm : lngen.
Hint Rewrite open_tm_wrt_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj_mutual :
(forall a2 a1 x1 n1,
  x1 `notin` fv_tm_tm a2 ->
  x1 `notin` fv_tm_tm a1 ->
  open_tm_wrt_tm_rec n1 (a_Var_f x1) a2 = open_tm_wrt_tm_rec n1 (a_Var_f x1) a1 ->
  a2 = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_inj :
forall a2 a1 x1 n1,
  x1 `notin` fv_tm_tm a2 ->
  x1 `notin` fv_tm_tm a1 ->
  open_tm_wrt_tm_rec n1 (a_Var_f x1) a2 = open_tm_wrt_tm_rec n1 (a_Var_f x1) a1 ->
  a2 = a1.
Proof. Admitted.

#[export] Hint Immediate open_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_inj :
forall a2 a1 x1,
  x1 `notin` fv_tm_tm a2 ->
  x1 `notin` fv_tm_tm a1 ->
  open_tm_wrt_tm a2 (a_Var_f x1) = open_tm_wrt_tm a1 (a_Var_f x1) ->
  a2 = a1.
Proof. Admitted.

#[export] Hint Immediate open_tm_wrt_tm_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_tm_wrt_tm_of_lc_tm_mutual :
(forall a1,
  lc_tm a1 ->
  degree_tm_wrt_tm 0 a1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_tm_of_lc_tm :
forall a1,
  lc_tm a1 ->
  degree_tm_wrt_tm 0 a1.
Proof. Admitted.

#[export] Hint Resolve degree_tm_wrt_tm_of_lc_tm : lngen.

(* begin hide *)

Lemma lc_tm_of_degree_size_mutual :
forall i1,
(forall a1,
  size_tm a1 = i1 ->
  degree_tm_wrt_tm 0 a1 ->
  lc_tm a1).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_of_degree :
forall a1,
  degree_tm_wrt_tm 0 a1 ->
  lc_tm a1.
Proof. Admitted.

#[export] Hint Resolve lc_tm_of_degree : lngen.

Ltac sort_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac grade_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac tm_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_tm_wrt_tm_of_lc_tm in J1; clear H
          end).

Lemma lc_a_Pi_exists :
forall x1 psi1 A1 B1,
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm B1 (a_Var_f x1)) ->
  lc_tm (a_Pi psi1 A1 B1).
Proof. Admitted.

Lemma lc_a_Abs_exists :
forall x1 psi1 A1 a1,
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm a1 (a_Var_f x1)) ->
  lc_tm (a_Abs psi1 A1 a1).
Proof. Admitted.

Lemma lc_a_WSigma_exists :
forall x1 psi1 A1 B1,
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm B1 (a_Var_f x1)) ->
  lc_tm (a_WSigma psi1 A1 B1).
Proof. Admitted.

Lemma lc_a_LetPair_exists :
forall x1 psi1 a1 b1,
  lc_tm a1 ->
  lc_tm (open_tm_wrt_tm b1 (a_Var_f x1)) ->
  lc_tm (a_LetPair psi1 a1 b1).
Proof. Admitted.

Lemma lc_a_SSigma_exists :
forall x1 psi1 A1 B1,
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm B1 (a_Var_f x1)) ->
  lc_tm (a_SSigma psi1 A1 B1).
Proof. Admitted.

#[export] Hint Extern 1 (lc_tm (a_Pi _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Pi_exists x1) : core.

#[export] Hint Extern 1 (lc_tm (a_Abs _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Abs_exists x1) : core.

#[export] Hint Extern 1 (lc_tm (a_WSigma _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_WSigma_exists x1) : core.

#[export] Hint Extern 1 (lc_tm (a_LetPair _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_LetPair_exists x1) : core.

#[export] Hint Extern 1 (lc_tm (a_SSigma _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_SSigma_exists x1) : core.

Lemma lc_body_tm_wrt_tm :
forall a1 a2,
  body_tm_wrt_tm a1 ->
  lc_tm a2 ->
  lc_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

#[export] Hint Resolve lc_body_tm_wrt_tm : lngen.

Lemma lc_body_a_Pi_3 :
forall psi1 A1 B1,
  lc_tm (a_Pi psi1 A1 B1) ->
  body_tm_wrt_tm B1.
Proof. Admitted.

#[export] Hint Resolve lc_body_a_Pi_3 : lngen.

Lemma lc_body_a_Abs_3 :
forall psi1 A1 a1,
  lc_tm (a_Abs psi1 A1 a1) ->
  body_tm_wrt_tm a1.
Proof. Admitted.

#[export] Hint Resolve lc_body_a_Abs_3 : lngen.

Lemma lc_body_a_WSigma_3 :
forall psi1 A1 B1,
  lc_tm (a_WSigma psi1 A1 B1) ->
  body_tm_wrt_tm B1.
Proof. Admitted.

#[export] Hint Resolve lc_body_a_WSigma_3 : lngen.

Lemma lc_body_a_LetPair_3 :
forall psi1 a1 b1,
  lc_tm (a_LetPair psi1 a1 b1) ->
  body_tm_wrt_tm b1.
Proof. Admitted.

#[export] Hint Resolve lc_body_a_LetPair_3 : lngen.

Lemma lc_body_a_SSigma_3 :
forall psi1 A1 B1,
  lc_tm (a_SSigma psi1 A1 B1) ->
  body_tm_wrt_tm B1.
Proof. Admitted.

#[export] Hint Resolve lc_body_a_SSigma_3 : lngen.

(* begin hide *)

Lemma lc_tm_unique_mutual :
(forall a1 (proof2 proof3 : lc_tm a1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_unique :
forall a1 (proof2 proof3 : lc_tm a1), proof2 = proof3.
Proof. Admitted.

#[export] Hint Resolve lc_tm_unique : lngen.

(* begin hide *)

Lemma lc_tm_of_lc_set_tm_mutual :
(forall a1, lc_set_tm a1 -> lc_tm a1).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_of_lc_set_tm :
forall a1, lc_set_tm a1 -> lc_tm a1.
Proof. Admitted.

#[export] Hint Resolve lc_tm_of_lc_set_tm : lngen.

(* begin hide *)

Lemma lc_set_tm_of_lc_tm_size_mutual :
forall i1,
(forall a1,
  size_tm a1 = i1 ->
  lc_tm a1 ->
  lc_set_tm a1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_tm_of_lc_tm :
forall a1,
  lc_tm a1 ->
  lc_set_tm a1.
Proof. Admitted.

#[export] Hint Resolve lc_set_tm_of_lc_tm : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual :
(forall a1 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 `notin` fv_tm_tm a1 ->
  close_tm_wrt_tm_rec n1 x1 a1 = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall a1 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 `notin` fv_tm_tm a1 ->
  close_tm_wrt_tm_rec n1 x1 a1 = a1.
Proof. Admitted.

#[export] Hint Resolve close_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
Hint Rewrite close_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

Lemma close_tm_wrt_tm_lc_tm :
forall a1 x1,
  lc_tm a1 ->
  x1 `notin` fv_tm_tm a1 ->
  close_tm_wrt_tm x1 a1 = a1.
Proof. Admitted.

#[export] Hint Resolve close_tm_wrt_tm_lc_tm : lngen.
Hint Rewrite close_tm_wrt_tm_lc_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm_mutual :
(forall a2 a1 n1,
  degree_tm_wrt_tm n1 a2 ->
  open_tm_wrt_tm_rec n1 a1 a2 = a2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_tm_rec_degree_tm_wrt_tm :
forall a2 a1 n1,
  degree_tm_wrt_tm n1 a2 ->
  open_tm_wrt_tm_rec n1 a1 a2 = a2.
Proof. Admitted.

#[export] Hint Resolve open_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
Hint Rewrite open_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

Lemma open_tm_wrt_tm_lc_tm :
forall a2 a1,
  lc_tm a2 ->
  open_tm_wrt_tm a2 a1 = a2.
Proof. Admitted.

#[export] Hint Resolve open_tm_wrt_tm_lc_tm : lngen.
Hint Rewrite open_tm_wrt_tm_lc_tm using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_tm_tm_close_tm_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  fv_tm_tm (close_tm_wrt_tm_rec n1 x1 a1) [=] remove x1 (fv_tm_tm a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  fv_tm_tm (close_tm_wrt_tm_rec n1 x1 a1) [=] remove x1 (fv_tm_tm a1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_close_tm_wrt_tm_rec : lngen.
Hint Rewrite fv_tm_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_tm_tm_close_tm_wrt_tm :
forall a1 x1,
  fv_tm_tm (close_tm_wrt_tm x1 a1) [=] remove x1 (fv_tm_tm a1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_close_tm_wrt_tm : lngen.
Hint Rewrite fv_tm_tm_close_tm_wrt_tm using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_tm_open_tm_wrt_tm_rec_lower_mutual :
(forall a1 a2 n1,
  fv_tm_tm a1 [<=] fv_tm_tm (open_tm_wrt_tm_rec n1 a2 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_open_tm_wrt_tm_rec_lower :
forall a1 a2 n1,
  fv_tm_tm a1 [<=] fv_tm_tm (open_tm_wrt_tm_rec n1 a2 a1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

Lemma fv_tm_tm_open_tm_wrt_tm_lower :
forall a1 a2,
  fv_tm_tm a1 [<=] fv_tm_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_open_tm_wrt_tm_lower : lngen.

(* begin hide *)

Lemma fv_tm_tm_open_tm_wrt_tm_rec_upper_mutual :
(forall a1 a2 n1,
  fv_tm_tm (open_tm_wrt_tm_rec n1 a2 a1) [<=] fv_tm_tm a2 `union` fv_tm_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_open_tm_wrt_tm_rec_upper :
forall a1 a2 n1,
  fv_tm_tm (open_tm_wrt_tm_rec n1 a2 a1) [<=] fv_tm_tm a2 `union` fv_tm_tm a1.
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

Lemma fv_tm_tm_open_tm_wrt_tm_upper :
forall a1 a2,
  fv_tm_tm (open_tm_wrt_tm a1 a2) [<=] fv_tm_tm a2 `union` fv_tm_tm a1.
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_open_tm_wrt_tm_upper : lngen.

(* begin hide *)

Lemma fv_tm_tm_subst_tm_tm_fresh_mutual :
(forall a1 a2 x1,
  x1 `notin` fv_tm_tm a1 ->
  fv_tm_tm (subst_tm_tm a2 x1 a1) [=] fv_tm_tm a1).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_subst_tm_tm_fresh :
forall a1 a2 x1,
  x1 `notin` fv_tm_tm a1 ->
  fv_tm_tm (subst_tm_tm a2 x1 a1) [=] fv_tm_tm a1.
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_subst_tm_tm_fresh : lngen.
Hint Rewrite fv_tm_tm_subst_tm_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_tm_tm_subst_tm_tm_lower_mutual :
(forall a1 a2 x1,
  remove x1 (fv_tm_tm a1) [<=] fv_tm_tm (subst_tm_tm a2 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_subst_tm_tm_lower :
forall a1 a2 x1,
  remove x1 (fv_tm_tm a1) [<=] fv_tm_tm (subst_tm_tm a2 x1 a1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_subst_tm_tm_lower : lngen.

(* begin hide *)

Lemma fv_tm_tm_subst_tm_tm_notin_mutual :
(forall a1 a2 x1 x2,
  x2 `notin` fv_tm_tm a1 ->
  x2 `notin` fv_tm_tm a2 ->
  x2 `notin` fv_tm_tm (subst_tm_tm a2 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_subst_tm_tm_notin :
forall a1 a2 x1 x2,
  x2 `notin` fv_tm_tm a1 ->
  x2 `notin` fv_tm_tm a2 ->
  x2 `notin` fv_tm_tm (subst_tm_tm a2 x1 a1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_subst_tm_tm_notin : lngen.

(* begin hide *)

Lemma fv_tm_tm_subst_tm_tm_upper_mutual :
(forall a1 a2 x1,
  fv_tm_tm (subst_tm_tm a2 x1 a1) [<=] fv_tm_tm a2 `union` remove x1 (fv_tm_tm a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_subst_tm_tm_upper :
forall a1 a2 x1,
  fv_tm_tm (subst_tm_tm a2 x1 a1) [<=] fv_tm_tm a2 `union` remove x1 (fv_tm_tm a1).
Proof. Admitted.

#[export] Hint Resolve fv_tm_tm_subst_tm_tm_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_tm_tm_close_tm_wrt_tm_rec_mutual :
(forall a2 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm a1 ->
  subst_tm_tm a1 x1 (close_tm_wrt_tm_rec n1 x2 a2) = close_tm_wrt_tm_rec n1 x2 (subst_tm_tm a1 x1 a2)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_close_tm_wrt_tm_rec :
forall a2 a1 x1 x2 n1,
  degree_tm_wrt_tm n1 a1 ->
  x1 <> x2 ->
  x2 `notin` fv_tm_tm a1 ->
  subst_tm_tm a1 x1 (close_tm_wrt_tm_rec n1 x2 a2) = close_tm_wrt_tm_rec n1 x2 (subst_tm_tm a1 x1 a2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_close_tm_wrt_tm_rec : lngen.

Lemma subst_tm_tm_close_tm_wrt_tm :
forall a2 a1 x1 x2,
  lc_tm a1 ->  x1 <> x2 ->
  x2 `notin` fv_tm_tm a1 ->
  subst_tm_tm a1 x1 (close_tm_wrt_tm x2 a2) = close_tm_wrt_tm x2 (subst_tm_tm a1 x1 a2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_close_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_tm_tm_degree_tm_wrt_tm_mutual :
(forall a1 a2 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 a2 ->
  degree_tm_wrt_tm n1 (subst_tm_tm a2 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_degree_tm_wrt_tm :
forall a1 a2 x1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 a2 ->
  degree_tm_wrt_tm n1 (subst_tm_tm a2 x1 a1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_degree_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_tm_tm_fresh_eq_mutual :
(forall a2 a1 x1,
  x1 `notin` fv_tm_tm a2 ->
  subst_tm_tm a1 x1 a2 = a2).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_fresh_eq :
forall a2 a1 x1,
  x1 `notin` fv_tm_tm a2 ->
  subst_tm_tm a1 x1 a2 = a2.
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_fresh_eq : lngen.
Hint Rewrite subst_tm_tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tm_tm_fresh_same_mutual :
(forall a2 a1 x1,
  x1 `notin` fv_tm_tm a1 ->
  x1 `notin` fv_tm_tm (subst_tm_tm a1 x1 a2)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_fresh_same :
forall a2 a1 x1,
  x1 `notin` fv_tm_tm a1 ->
  x1 `notin` fv_tm_tm (subst_tm_tm a1 x1 a2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_tm_tm_fresh_mutual :
(forall a2 a1 x1 x2,
  x1 `notin` fv_tm_tm a2 ->
  x1 `notin` fv_tm_tm a1 ->
  x1 `notin` fv_tm_tm (subst_tm_tm a1 x2 a2)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_fresh :
forall a2 a1 x1 x2,
  x1 `notin` fv_tm_tm a2 ->
  x1 `notin` fv_tm_tm a1 ->
  x1 `notin` fv_tm_tm (subst_tm_tm a1 x2 a2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_fresh : lngen.

Lemma subst_tm_tm_lc_tm :
forall a1 a2 x1,
  lc_tm a1 ->
  lc_tm a2 ->
  lc_tm (subst_tm_tm a2 x1 a1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_lc_tm : lngen.

(* begin hide *)

Lemma subst_tm_tm_open_tm_wrt_tm_rec_mutual :
(forall a3 a1 a2 x1 n1,
  lc_tm a1 ->
  subst_tm_tm a1 x1 (open_tm_wrt_tm_rec n1 a2 a3) = open_tm_wrt_tm_rec n1 (subst_tm_tm a1 x1 a2) (subst_tm_tm a1 x1 a3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_tm_tm_open_tm_wrt_tm_rec :
forall a3 a1 a2 x1 n1,
  lc_tm a1 ->
  subst_tm_tm a1 x1 (open_tm_wrt_tm_rec n1 a2 a3) = open_tm_wrt_tm_rec n1 (subst_tm_tm a1 x1 a2) (subst_tm_tm a1 x1 a3).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma subst_tm_tm_open_tm_wrt_tm :
forall a3 a1 a2 x1,
  lc_tm a1 ->
  subst_tm_tm a1 x1 (open_tm_wrt_tm a3 a2) = open_tm_wrt_tm (subst_tm_tm a1 x1 a3) (subst_tm_tm a1 x1 a2).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_tm_open_tm_wrt_tm_var :
forall a2 a1 x1 x2,
  x1 <> x2 ->
  lc_tm a1 ->
  open_tm_wrt_tm (subst_tm_tm a1 x1 a2) (a_Var_f x2) = subst_tm_tm a1 x1 (open_tm_wrt_tm a2 (a_Var_f x2)).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_open_tm_wrt_tm_var : lngen.

(* begin hide *)

Lemma subst_tm_tm_spec_rec_mutual :
(forall a1 a2 x1 n1,
  subst_tm_tm a2 x1 a1 = open_tm_wrt_tm_rec n1 a2 (close_tm_wrt_tm_rec n1 x1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_tm_tm_spec_rec :
forall a1 a2 x1 n1,
  subst_tm_tm a2 x1 a1 = open_tm_wrt_tm_rec n1 a2 (close_tm_wrt_tm_rec n1 x1 a1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_spec_rec : lngen.

(* end hide *)

Lemma subst_tm_tm_spec :
forall a1 a2 x1,
  subst_tm_tm a2 x1 a1 = open_tm_wrt_tm (close_tm_wrt_tm x1 a1) a2.
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_spec : lngen.

(* begin hide *)

Lemma subst_tm_tm_subst_tm_tm_mutual :
(forall a1 a2 a3 x2 x1,
  x2 `notin` fv_tm_tm a2 ->
  x2 <> x1 ->
  subst_tm_tm a2 x1 (subst_tm_tm a3 x2 a1) = subst_tm_tm (subst_tm_tm a2 x1 a3) x2 (subst_tm_tm a2 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_subst_tm_tm :
forall a1 a2 a3 x2 x1,
  x2 `notin` fv_tm_tm a2 ->
  x2 <> x1 ->
  subst_tm_tm a2 x1 (subst_tm_tm a3 x2 a1) = subst_tm_tm (subst_tm_tm a2 x1 a3) x2 (subst_tm_tm a2 x1 a1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_subst_tm_tm : lngen.

(* begin hide *)

Lemma subst_tm_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall a2 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm a2 ->
  x2 `notin` fv_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  subst_tm_tm a1 x1 a2 = close_tm_wrt_tm_rec n1 x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x2) a2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_tm_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall a2 a1 x1 x2 n1,
  x2 `notin` fv_tm_tm a2 ->
  x2 `notin` fv_tm_tm a1 ->
  x2 <> x1 ->
  degree_tm_wrt_tm n1 a1 ->
  subst_tm_tm a1 x1 a2 = close_tm_wrt_tm_rec n1 x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x2) a2)).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

Lemma subst_tm_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall a2 a1 x1 x2,
  x2 `notin` fv_tm_tm a2 ->
  x2 `notin` fv_tm_tm a1 ->
  x2 <> x1 ->
  lc_tm a1 ->
  subst_tm_tm a1 x1 a2 = close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm a2 (a_Var_f x2))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_tm_a_Pi :
forall x2 psi1 A1 B1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm B1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_Pi psi1 A1 B1) = a_Pi (psi1) (subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm B1 (a_Var_f x2)))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_a_Pi : lngen.

Lemma subst_tm_tm_a_Abs :
forall x2 psi1 A1 a2 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm a2 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_Abs psi1 A1 a2) = a_Abs (psi1) (subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm a2 (a_Var_f x2)))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_a_Abs : lngen.

Lemma subst_tm_tm_a_WSigma :
forall x2 psi1 A1 B1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm B1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_WSigma psi1 A1 B1) = a_WSigma (psi1) (subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm B1 (a_Var_f x2)))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_a_WSigma : lngen.

Lemma subst_tm_tm_a_LetPair :
forall x2 psi1 a2 b1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm b1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_LetPair psi1 a2 b1) = a_LetPair (psi1) (subst_tm_tm a1 x1 a2) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm b1 (a_Var_f x2)))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_a_LetPair : lngen.

Lemma subst_tm_tm_a_SSigma :
forall x2 psi1 A1 B1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm B1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_SSigma psi1 A1 B1) = a_SSigma (psi1) (subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm B1 (a_Var_f x2)))).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_a_SSigma : lngen.

(* begin hide *)

Lemma subst_tm_tm_intro_rec_mutual :
(forall a1 x1 a2 n1,
  x1 `notin` fv_tm_tm a1 ->
  open_tm_wrt_tm_rec n1 a2 a1 = subst_tm_tm a2 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_intro_rec :
forall a1 x1 a2 n1,
  x1 `notin` fv_tm_tm a1 ->
  open_tm_wrt_tm_rec n1 a2 a1 = subst_tm_tm a2 x1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_intro_rec : lngen.
Hint Rewrite subst_tm_tm_intro_rec using solve [auto] : lngen.

Lemma subst_tm_tm_intro :
forall x1 a1 a2,
  x1 `notin` fv_tm_tm a1 ->
  open_tm_wrt_tm a1 a2 = subst_tm_tm a2 x1 (open_tm_wrt_tm a1 (a_Var_f x1)).
Proof. Admitted.

#[export] Hint Resolve subst_tm_tm_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
