Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export dqtt_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme qexp_ind' := Induction for qexp Sort Prop.

Definition qexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  qexp_ind' H1 H2 H3 H4 H5 H6.

Scheme qexp_rec' := Induction for qexp Sort Set.

Definition qexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  qexp_rec' H1 H2 H3 H4 H5 H6.

Scheme tm_ind' := Induction for tm Sort Prop.

Definition tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 =>
  tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24.

Scheme tm_rec' := Induction for tm Sort Set.

Definition tm_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 =>
  tm_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_qexp_wrt_qexp_rec (n1 : nat) (m1 : qvar) (q1 : qexp) {struct q1} : qexp :=
  match q1 with
    | q_Var_f m2 => if (m1 == m2) then (q_Var_b n1) else (q_Var_f m2)
    | q_Var_b n2 => if (lt_ge_dec n2 n1) then (q_Var_b n2) else (q_Var_b (S n2))
    | q_Const u1 => q_Const u1
    | q_Plus q2 q3 => q_Plus (close_qexp_wrt_qexp_rec n1 m1 q2) (close_qexp_wrt_qexp_rec n1 m1 q3)
    | q_Mul q2 q3 => q_Mul (close_qexp_wrt_qexp_rec n1 m1 q2) (close_qexp_wrt_qexp_rec n1 m1 q3)
  end.

Definition close_qexp_wrt_qexp m1 q1 := close_qexp_wrt_qexp_rec 0 m1 q1.

Fixpoint close_tm_wrt_tm_rec (n1 : nat) (x1 : tmvar) (a1 : tm) {struct a1} : tm :=
  match a1 with
    | a_TyUnit => a_TyUnit
    | a_TmUnit => a_TmUnit
    | a_letunitB a2 b1 B1 => a_letunitB (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_Pi q1 A1 B1 => a_Pi q1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_Lam q1 A1 a2 => a_Lam q1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 a2)
    | a_App a2 b1 => a_App (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Box q1 A1 => a_Box q1 (close_tm_wrt_tm_rec n1 x1 A1)
    | a_LetBoxB a2 b1 B1 => a_LetBoxB (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec (S n1) x1 b1) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_Type => a_Type
    | a_Var_f x2 => if (x1 == x2) then (a_Var_b n1) else (a_Var_f x2)
    | a_Var_b n2 => if (lt_ge_dec n2 n1) then (a_Var_b n2) else (a_Var_b (S n2))
    | a_box q1 a2 => a_box q1 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Let a2 b1 => a_Let (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec (S n1) x1 b1)
    | a_Sum A1 A2 => a_Sum (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec n1 x1 A2)
    | a_Inj1 a2 => a_Inj1 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Inj2 a2 => a_Inj2 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Case q1 a2 b1 b2 B1 => a_Case q1 (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1) (close_tm_wrt_tm_rec n1 x1 b2) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_Sigma q1 A1 B1 => a_Sigma q1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_Tensor a2 b1 => a_Tensor (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Spread a2 b1 B1 => a_Spread (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec (S n1) x1 b1) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_AllU A1 => a_AllU (close_tm_wrt_tm_rec n1 x1 A1)
    | a_LamU a2 => a_LamU (close_tm_wrt_tm_rec n1 x1 a2)
    | a_AppU a2 q1 => a_AppU (close_tm_wrt_tm_rec n1 x1 a2) q1
  end.

Fixpoint close_tm_wrt_qexp_rec (n1 : nat) (m1 : qvar) (a1 : tm) {struct a1} : tm :=
  match a1 with
    | a_TyUnit => a_TyUnit
    | a_TmUnit => a_TmUnit
    | a_letunitB a2 b1 B1 => a_letunitB (close_tm_wrt_qexp_rec n1 m1 a2) (close_tm_wrt_qexp_rec n1 m1 b1) (close_tm_wrt_qexp_rec n1 m1 B1)
    | a_Pi q1 A1 B1 => a_Pi (close_qexp_wrt_qexp_rec n1 m1 q1) (close_tm_wrt_qexp_rec n1 m1 A1) (close_tm_wrt_qexp_rec n1 m1 B1)
    | a_Lam q1 A1 a2 => a_Lam (close_qexp_wrt_qexp_rec n1 m1 q1) (close_tm_wrt_qexp_rec n1 m1 A1) (close_tm_wrt_qexp_rec n1 m1 a2)
    | a_App a2 b1 => a_App (close_tm_wrt_qexp_rec n1 m1 a2) (close_tm_wrt_qexp_rec n1 m1 b1)
    | a_Box q1 A1 => a_Box (close_qexp_wrt_qexp_rec n1 m1 q1) (close_tm_wrt_qexp_rec n1 m1 A1)
    | a_LetBoxB a2 b1 B1 => a_LetBoxB (close_tm_wrt_qexp_rec n1 m1 a2) (close_tm_wrt_qexp_rec n1 m1 b1) (close_tm_wrt_qexp_rec n1 m1 B1)
    | a_Type => a_Type
    | a_Var_f x1 => a_Var_f x1
    | a_Var_b n2 => a_Var_b n2
    | a_box q1 a2 => a_box (close_qexp_wrt_qexp_rec n1 m1 q1) (close_tm_wrt_qexp_rec n1 m1 a2)
    | a_Let a2 b1 => a_Let (close_tm_wrt_qexp_rec n1 m1 a2) (close_tm_wrt_qexp_rec n1 m1 b1)
    | a_Sum A1 A2 => a_Sum (close_tm_wrt_qexp_rec n1 m1 A1) (close_tm_wrt_qexp_rec n1 m1 A2)
    | a_Inj1 a2 => a_Inj1 (close_tm_wrt_qexp_rec n1 m1 a2)
    | a_Inj2 a2 => a_Inj2 (close_tm_wrt_qexp_rec n1 m1 a2)
    | a_Case q1 a2 b1 b2 B1 => a_Case (close_qexp_wrt_qexp_rec n1 m1 q1) (close_tm_wrt_qexp_rec n1 m1 a2) (close_tm_wrt_qexp_rec n1 m1 b1) (close_tm_wrt_qexp_rec n1 m1 b2) (close_tm_wrt_qexp_rec n1 m1 B1)
    | a_Sigma q1 A1 B1 => a_Sigma (close_qexp_wrt_qexp_rec n1 m1 q1) (close_tm_wrt_qexp_rec n1 m1 A1) (close_tm_wrt_qexp_rec n1 m1 B1)
    | a_Tensor a2 b1 => a_Tensor (close_tm_wrt_qexp_rec n1 m1 a2) (close_tm_wrt_qexp_rec n1 m1 b1)
    | a_Spread a2 b1 B1 => a_Spread (close_tm_wrt_qexp_rec n1 m1 a2) (close_tm_wrt_qexp_rec n1 m1 b1) (close_tm_wrt_qexp_rec n1 m1 B1)
    | a_AllU A1 => a_AllU (close_tm_wrt_qexp_rec (S n1) m1 A1)
    | a_LamU a2 => a_LamU (close_tm_wrt_qexp_rec (S n1) m1 a2)
    | a_AppU a2 q1 => a_AppU (close_tm_wrt_qexp_rec n1 m1 a2) (close_qexp_wrt_qexp_rec n1 m1 q1)
  end.

Definition close_tm_wrt_tm x1 a1 := close_tm_wrt_tm_rec 0 x1 a1.

Definition close_tm_wrt_qexp m1 a1 := close_tm_wrt_qexp_rec 0 m1 a1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_qexp (q1 : qexp) {struct q1} : nat :=
  match q1 with
    | q_Var_f m1 => 1
    | q_Var_b n1 => 1
    | q_Const u1 => 1
    | q_Plus q2 q3 => 1 + (size_qexp q2) + (size_qexp q3)
    | q_Mul q2 q3 => 1 + (size_qexp q2) + (size_qexp q3)
  end.

Fixpoint size_tm (a1 : tm) {struct a1} : nat :=
  match a1 with
    | a_TyUnit => 1
    | a_TmUnit => 1
    | a_letunitB a2 b1 B1 => 1 + (size_tm a2) + (size_tm b1) + (size_tm B1)
    | a_Pi q1 A1 B1 => 1 + (size_qexp q1) + (size_tm A1) + (size_tm B1)
    | a_Lam q1 A1 a2 => 1 + (size_qexp q1) + (size_tm A1) + (size_tm a2)
    | a_App a2 b1 => 1 + (size_tm a2) + (size_tm b1)
    | a_Box q1 A1 => 1 + (size_qexp q1) + (size_tm A1)
    | a_LetBoxB a2 b1 B1 => 1 + (size_tm a2) + (size_tm b1) + (size_tm B1)
    | a_Type => 1
    | a_Var_f x1 => 1
    | a_Var_b n1 => 1
    | a_box q1 a2 => 1 + (size_qexp q1) + (size_tm a2)
    | a_Let a2 b1 => 1 + (size_tm a2) + (size_tm b1)
    | a_Sum A1 A2 => 1 + (size_tm A1) + (size_tm A2)
    | a_Inj1 a2 => 1 + (size_tm a2)
    | a_Inj2 a2 => 1 + (size_tm a2)
    | a_Case q1 a2 b1 b2 B1 => 1 + (size_qexp q1) + (size_tm a2) + (size_tm b1) + (size_tm b2) + (size_tm B1)
    | a_Sigma q1 A1 B1 => 1 + (size_qexp q1) + (size_tm A1) + (size_tm B1)
    | a_Tensor a2 b1 => 1 + (size_tm a2) + (size_tm b1)
    | a_Spread a2 b1 B1 => 1 + (size_tm a2) + (size_tm b1) + (size_tm B1)
    | a_AllU A1 => 1 + (size_tm A1)
    | a_LamU a2 => 1 + (size_tm a2)
    | a_AppU a2 q1 => 1 + (size_tm a2) + (size_qexp q1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_qexp_wrt_qexp : nat -> qexp -> Prop :=
  | degree_wrt_qexp_q_Var_f : forall n1 m1,
    degree_qexp_wrt_qexp n1 (q_Var_f m1)
  | degree_wrt_qexp_q_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_qexp_wrt_qexp n1 (q_Var_b n2)
  | degree_wrt_qexp_q_Const : forall n1 u1,
    degree_qexp_wrt_qexp n1 (q_Const u1)
  | degree_wrt_qexp_q_Plus : forall n1 q1 q2,
    degree_qexp_wrt_qexp n1 q1 ->
    degree_qexp_wrt_qexp n1 q2 ->
    degree_qexp_wrt_qexp n1 (q_Plus q1 q2)
  | degree_wrt_qexp_q_Mul : forall n1 q1 q2,
    degree_qexp_wrt_qexp n1 q1 ->
    degree_qexp_wrt_qexp n1 q2 ->
    degree_qexp_wrt_qexp n1 (q_Mul q1 q2).

Scheme degree_qexp_wrt_qexp_ind' := Induction for degree_qexp_wrt_qexp Sort Prop.

Definition degree_qexp_wrt_qexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  degree_qexp_wrt_qexp_ind' H1 H2 H3 H4 H5 H6.

Hint Constructors degree_qexp_wrt_qexp : core lngen.

Inductive degree_tm_wrt_tm : nat -> tm -> Prop :=
  | degree_wrt_tm_a_TyUnit : forall n1,
    degree_tm_wrt_tm n1 (a_TyUnit)
  | degree_wrt_tm_a_TmUnit : forall n1,
    degree_tm_wrt_tm n1 (a_TmUnit)
  | degree_wrt_tm_a_letunitB : forall n1 a1 b1 B1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 B1 ->
    degree_tm_wrt_tm n1 (a_letunitB a1 b1 B1)
  | degree_wrt_tm_a_Pi : forall n1 q1 A1 B1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) B1 ->
    degree_tm_wrt_tm n1 (a_Pi q1 A1 B1)
  | degree_wrt_tm_a_Lam : forall n1 q1 A1 a1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) a1 ->
    degree_tm_wrt_tm n1 (a_Lam q1 A1 a1)
  | degree_wrt_tm_a_App : forall n1 a1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_App a1 b1)
  | degree_wrt_tm_a_Box : forall n1 q1 A1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm n1 (a_Box q1 A1)
  | degree_wrt_tm_a_LetBoxB : forall n1 a1 b1 B1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm (S n1) b1 ->
    degree_tm_wrt_tm n1 B1 ->
    degree_tm_wrt_tm n1 (a_LetBoxB a1 b1 B1)
  | degree_wrt_tm_a_Type : forall n1,
    degree_tm_wrt_tm n1 (a_Type)
  | degree_wrt_tm_a_Var_f : forall n1 x1,
    degree_tm_wrt_tm n1 (a_Var_f x1)
  | degree_wrt_tm_a_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_tm_wrt_tm n1 (a_Var_b n2)
  | degree_wrt_tm_a_box : forall n1 q1 a1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 (a_box q1 a1)
  | degree_wrt_tm_a_Let : forall n1 a1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm (S n1) b1 ->
    degree_tm_wrt_tm n1 (a_Let a1 b1)
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
  | degree_wrt_tm_a_Case : forall n1 q1 a1 b1 b2 B1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 b2 ->
    degree_tm_wrt_tm n1 B1 ->
    degree_tm_wrt_tm n1 (a_Case q1 a1 b1 b2 B1)
  | degree_wrt_tm_a_Sigma : forall n1 q1 A1 B1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm (S n1) B1 ->
    degree_tm_wrt_tm n1 (a_Sigma q1 A1 B1)
  | degree_wrt_tm_a_Tensor : forall n1 a1 b1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 b1 ->
    degree_tm_wrt_tm n1 (a_Tensor a1 b1)
  | degree_wrt_tm_a_Spread : forall n1 a1 b1 B1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm (S n1) b1 ->
    degree_tm_wrt_tm n1 B1 ->
    degree_tm_wrt_tm n1 (a_Spread a1 b1 B1)
  | degree_wrt_tm_a_AllU : forall n1 A1,
    degree_tm_wrt_tm n1 A1 ->
    degree_tm_wrt_tm n1 (a_AllU A1)
  | degree_wrt_tm_a_LamU : forall n1 a1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 (a_LamU a1)
  | degree_wrt_tm_a_AppU : forall n1 a1 q1,
    degree_tm_wrt_tm n1 a1 ->
    degree_tm_wrt_tm n1 (a_AppU a1 q1).

Inductive degree_tm_wrt_qexp : nat -> tm -> Prop :=
  | degree_wrt_qexp_a_TyUnit : forall n1,
    degree_tm_wrt_qexp n1 (a_TyUnit)
  | degree_wrt_qexp_a_TmUnit : forall n1,
    degree_tm_wrt_qexp n1 (a_TmUnit)
  | degree_wrt_qexp_a_letunitB : forall n1 a1 b1 B1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 b1 ->
    degree_tm_wrt_qexp n1 B1 ->
    degree_tm_wrt_qexp n1 (a_letunitB a1 b1 B1)
  | degree_wrt_qexp_a_Pi : forall n1 q1 A1 B1,
    degree_qexp_wrt_qexp n1 q1 ->
    degree_tm_wrt_qexp n1 A1 ->
    degree_tm_wrt_qexp n1 B1 ->
    degree_tm_wrt_qexp n1 (a_Pi q1 A1 B1)
  | degree_wrt_qexp_a_Lam : forall n1 q1 A1 a1,
    degree_qexp_wrt_qexp n1 q1 ->
    degree_tm_wrt_qexp n1 A1 ->
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 (a_Lam q1 A1 a1)
  | degree_wrt_qexp_a_App : forall n1 a1 b1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 b1 ->
    degree_tm_wrt_qexp n1 (a_App a1 b1)
  | degree_wrt_qexp_a_Box : forall n1 q1 A1,
    degree_qexp_wrt_qexp n1 q1 ->
    degree_tm_wrt_qexp n1 A1 ->
    degree_tm_wrt_qexp n1 (a_Box q1 A1)
  | degree_wrt_qexp_a_LetBoxB : forall n1 a1 b1 B1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 b1 ->
    degree_tm_wrt_qexp n1 B1 ->
    degree_tm_wrt_qexp n1 (a_LetBoxB a1 b1 B1)
  | degree_wrt_qexp_a_Type : forall n1,
    degree_tm_wrt_qexp n1 (a_Type)
  | degree_wrt_qexp_a_Var_f : forall n1 x1,
    degree_tm_wrt_qexp n1 (a_Var_f x1)
  | degree_wrt_qexp_a_Var_b : forall n1 n2,
    degree_tm_wrt_qexp n1 (a_Var_b n2)
  | degree_wrt_qexp_a_box : forall n1 q1 a1,
    degree_qexp_wrt_qexp n1 q1 ->
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 (a_box q1 a1)
  | degree_wrt_qexp_a_Let : forall n1 a1 b1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 b1 ->
    degree_tm_wrt_qexp n1 (a_Let a1 b1)
  | degree_wrt_qexp_a_Sum : forall n1 A1 A2,
    degree_tm_wrt_qexp n1 A1 ->
    degree_tm_wrt_qexp n1 A2 ->
    degree_tm_wrt_qexp n1 (a_Sum A1 A2)
  | degree_wrt_qexp_a_Inj1 : forall n1 a1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 (a_Inj1 a1)
  | degree_wrt_qexp_a_Inj2 : forall n1 a1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 (a_Inj2 a1)
  | degree_wrt_qexp_a_Case : forall n1 q1 a1 b1 b2 B1,
    degree_qexp_wrt_qexp n1 q1 ->
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 b1 ->
    degree_tm_wrt_qexp n1 b2 ->
    degree_tm_wrt_qexp n1 B1 ->
    degree_tm_wrt_qexp n1 (a_Case q1 a1 b1 b2 B1)
  | degree_wrt_qexp_a_Sigma : forall n1 q1 A1 B1,
    degree_qexp_wrt_qexp n1 q1 ->
    degree_tm_wrt_qexp n1 A1 ->
    degree_tm_wrt_qexp n1 B1 ->
    degree_tm_wrt_qexp n1 (a_Sigma q1 A1 B1)
  | degree_wrt_qexp_a_Tensor : forall n1 a1 b1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 b1 ->
    degree_tm_wrt_qexp n1 (a_Tensor a1 b1)
  | degree_wrt_qexp_a_Spread : forall n1 a1 b1 B1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_tm_wrt_qexp n1 b1 ->
    degree_tm_wrt_qexp n1 B1 ->
    degree_tm_wrt_qexp n1 (a_Spread a1 b1 B1)
  | degree_wrt_qexp_a_AllU : forall n1 A1,
    degree_tm_wrt_qexp (S n1) A1 ->
    degree_tm_wrt_qexp n1 (a_AllU A1)
  | degree_wrt_qexp_a_LamU : forall n1 a1,
    degree_tm_wrt_qexp (S n1) a1 ->
    degree_tm_wrt_qexp n1 (a_LamU a1)
  | degree_wrt_qexp_a_AppU : forall n1 a1 q1,
    degree_tm_wrt_qexp n1 a1 ->
    degree_qexp_wrt_qexp n1 q1 ->
    degree_tm_wrt_qexp n1 (a_AppU a1 q1).

Scheme degree_tm_wrt_tm_ind' := Induction for degree_tm_wrt_tm Sort Prop.

Definition degree_tm_wrt_tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 =>
  degree_tm_wrt_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24.

Scheme degree_tm_wrt_qexp_ind' := Induction for degree_tm_wrt_qexp Sort Prop.

Definition degree_tm_wrt_qexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 =>
  degree_tm_wrt_qexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24.

Hint Constructors degree_tm_wrt_tm : core lngen.

Hint Constructors degree_tm_wrt_qexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_qexp : qexp -> Set :=
  | lc_set_q_Var_f : forall m1,
    lc_set_qexp (q_Var_f m1)
  | lc_set_q_Const : forall u1,
    lc_set_qexp (q_Const u1)
  | lc_set_q_Plus : forall q1 q2,
    lc_set_qexp q1 ->
    lc_set_qexp q2 ->
    lc_set_qexp (q_Plus q1 q2)
  | lc_set_q_Mul : forall q1 q2,
    lc_set_qexp q1 ->
    lc_set_qexp q2 ->
    lc_set_qexp (q_Mul q1 q2).

Scheme lc_qexp_ind' := Induction for lc_qexp Sort Prop.

Definition lc_qexp_mutind :=
  fun H1 H2 H3 H4 H5 =>
  lc_qexp_ind' H1 H2 H3 H4 H5.

Scheme lc_set_qexp_ind' := Induction for lc_set_qexp Sort Prop.

Definition lc_set_qexp_mutind :=
  fun H1 H2 H3 H4 H5 =>
  lc_set_qexp_ind' H1 H2 H3 H4 H5.

Scheme lc_set_qexp_rec' := Induction for lc_set_qexp Sort Set.

Definition lc_set_qexp_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  lc_set_qexp_rec' H1 H2 H3 H4 H5.

Hint Constructors lc_qexp : core lngen.

Hint Constructors lc_set_qexp : core lngen.

Inductive lc_set_tm : tm -> Set :=
  | lc_set_a_TyUnit :
    lc_set_tm (a_TyUnit)
  | lc_set_a_TmUnit :
    lc_set_tm (a_TmUnit)
  | lc_set_a_letunitB : forall a1 b1 B1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm B1 ->
    lc_set_tm (a_letunitB a1 b1 B1)
  | lc_set_a_Pi : forall q1 A1 B1,
    lc_set_qexp q1 ->
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm B1 (a_Var_f x1))) ->
    lc_set_tm (a_Pi q1 A1 B1)
  | lc_set_a_Lam : forall q1 A1 a1,
    lc_set_qexp q1 ->
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm a1 (a_Var_f x1))) ->
    lc_set_tm (a_Lam q1 A1 a1)
  | lc_set_a_App : forall a1 b1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm (a_App a1 b1)
  | lc_set_a_Box : forall q1 A1,
    lc_set_qexp q1 ->
    lc_set_tm A1 ->
    lc_set_tm (a_Box q1 A1)
  | lc_set_a_LetBoxB : forall a1 b1 B1,
    lc_set_tm a1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm b1 (a_Var_f x1))) ->
    lc_set_tm B1 ->
    lc_set_tm (a_LetBoxB a1 b1 B1)
  | lc_set_a_Type :
    lc_set_tm (a_Type)
  | lc_set_a_Var_f : forall x1,
    lc_set_tm (a_Var_f x1)
  | lc_set_a_box : forall q1 a1,
    lc_set_qexp q1 ->
    lc_set_tm a1 ->
    lc_set_tm (a_box q1 a1)
  | lc_set_a_Let : forall a1 b1,
    lc_set_tm a1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm b1 (a_Var_f x1))) ->
    lc_set_tm (a_Let a1 b1)
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
  | lc_set_a_Case : forall q1 a1 b1 b2 B1,
    lc_set_qexp q1 ->
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm b2 ->
    lc_set_tm B1 ->
    lc_set_tm (a_Case q1 a1 b1 b2 B1)
  | lc_set_a_Sigma : forall q1 A1 B1,
    lc_set_qexp q1 ->
    lc_set_tm A1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm B1 (a_Var_f x1))) ->
    lc_set_tm (a_Sigma q1 A1 B1)
  | lc_set_a_Tensor : forall a1 b1,
    lc_set_tm a1 ->
    lc_set_tm b1 ->
    lc_set_tm (a_Tensor a1 b1)
  | lc_set_a_Spread : forall a1 b1 B1,
    lc_set_tm a1 ->
    (forall x1 : tmvar, lc_set_tm (open_tm_wrt_tm b1 (a_Var_f x1))) ->
    lc_set_tm B1 ->
    lc_set_tm (a_Spread a1 b1 B1)
  | lc_set_a_AllU : forall A1,
    (forall m1 : qvar, lc_set_tm (open_tm_wrt_qexp A1 (q_Var_f m1))) ->
    lc_set_tm (a_AllU A1)
  | lc_set_a_LamU : forall a1,
    (forall m1 : qvar, lc_set_tm (open_tm_wrt_qexp a1 (q_Var_f m1))) ->
    lc_set_tm (a_LamU a1)
  | lc_set_a_AppU : forall a1 q1,
    lc_set_tm a1 ->
    lc_set_qexp q1 ->
    lc_set_tm (a_AppU a1 q1).

Scheme lc_tm_ind' := Induction for lc_tm Sort Prop.

Definition lc_tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 =>
  lc_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.

Scheme lc_set_tm_ind' := Induction for lc_set_tm Sort Prop.

Definition lc_set_tm_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 =>
  lc_set_tm_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.

Scheme lc_set_tm_rec' := Induction for lc_set_tm Sort Set.

Definition lc_set_tm_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 =>
  lc_set_tm_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23.

Hint Constructors lc_tm : core lngen.

Hint Constructors lc_set_tm : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_qexp_wrt_qexp q1 := forall m1, lc_qexp (open_qexp_wrt_qexp q1 (q_Var_f m1)).

Hint Unfold body_qexp_wrt_qexp : core.

Definition body_tm_wrt_tm a1 := forall x1, lc_tm (open_tm_wrt_tm a1 (a_Var_f x1)).

Definition body_tm_wrt_qexp a1 := forall m1, lc_tm (open_tm_wrt_qexp a1 (q_Var_f m1)).

Hint Unfold body_tm_wrt_tm : core.

Hint Unfold body_tm_wrt_qexp : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

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

Lemma size_qexp_min_mutual :
(forall q1, 1 <= size_qexp q1).
Proof. Admitted.

(* end hide *)

Lemma size_qexp_min :
forall q1, 1 <= size_qexp q1.
Proof. Admitted.

Hint Resolve size_qexp_min : lngen.

(* begin hide *)

Lemma size_tm_min_mutual :
(forall a1, 1 <= size_tm a1).
Proof. Admitted.

(* end hide *)

Lemma size_tm_min :
forall a1, 1 <= size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_min : lngen.

(* begin hide *)

Lemma size_qexp_close_qexp_wrt_qexp_rec_mutual :
(forall q1 m1 n1,
  size_qexp (close_qexp_wrt_qexp_rec n1 m1 q1) = size_qexp q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_qexp_close_qexp_wrt_qexp_rec :
forall q1 m1 n1,
  size_qexp (close_qexp_wrt_qexp_rec n1 m1 q1) = size_qexp q1.
Proof. Admitted.

Hint Resolve size_qexp_close_qexp_wrt_qexp_rec : lngen.
Hint Rewrite size_qexp_close_qexp_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

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

Hint Resolve size_tm_close_tm_wrt_tm_rec : lngen.
Hint Rewrite size_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_qexp_rec_mutual :
(forall a1 m1 n1,
  size_tm (close_tm_wrt_qexp_rec n1 m1 a1) = size_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_close_tm_wrt_qexp_rec :
forall a1 m1 n1,
  size_tm (close_tm_wrt_qexp_rec n1 m1 a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_close_tm_wrt_qexp_rec : lngen.
Hint Rewrite size_tm_close_tm_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_qexp_close_qexp_wrt_qexp :
forall q1 m1,
  size_qexp (close_qexp_wrt_qexp m1 q1) = size_qexp q1.
Proof. Admitted.

Hint Resolve size_qexp_close_qexp_wrt_qexp : lngen.
Hint Rewrite size_qexp_close_qexp_wrt_qexp using solve [auto] : lngen.

Lemma size_tm_close_tm_wrt_tm :
forall a1 x1,
  size_tm (close_tm_wrt_tm x1 a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_close_tm_wrt_tm : lngen.
Hint Rewrite size_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma size_tm_close_tm_wrt_qexp :
forall a1 m1,
  size_tm (close_tm_wrt_qexp m1 a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_close_tm_wrt_qexp : lngen.
Hint Rewrite size_tm_close_tm_wrt_qexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_qexp_open_qexp_wrt_qexp_rec_mutual :
(forall q1 q2 n1,
  size_qexp q1 <= size_qexp (open_qexp_wrt_qexp_rec n1 q2 q1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_qexp_open_qexp_wrt_qexp_rec :
forall q1 q2 n1,
  size_qexp q1 <= size_qexp (open_qexp_wrt_qexp_rec n1 q2 q1).
Proof. Admitted.

Hint Resolve size_qexp_open_qexp_wrt_qexp_rec : lngen.

(* end hide *)

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

Hint Resolve size_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_qexp_rec_mutual :
(forall a1 q1 n1,
  size_tm a1 <= size_tm (open_tm_wrt_qexp_rec n1 q1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_qexp_rec :
forall a1 q1 n1,
  size_tm a1 <= size_tm (open_tm_wrt_qexp_rec n1 q1 a1).
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_qexp_rec : lngen.

(* end hide *)

Lemma size_qexp_open_qexp_wrt_qexp :
forall q1 q2,
  size_qexp q1 <= size_qexp (open_qexp_wrt_qexp q1 q2).
Proof. Admitted.

Hint Resolve size_qexp_open_qexp_wrt_qexp : lngen.

Lemma size_tm_open_tm_wrt_tm :
forall a1 a2,
  size_tm a1 <= size_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_tm : lngen.

Lemma size_tm_open_tm_wrt_qexp :
forall a1 q1,
  size_tm a1 <= size_tm (open_tm_wrt_qexp a1 q1).
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_qexp : lngen.

(* begin hide *)

Lemma size_qexp_open_qexp_wrt_qexp_rec_var_mutual :
(forall q1 m1 n1,
  size_qexp (open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q1) = size_qexp q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_qexp_open_qexp_wrt_qexp_rec_var :
forall q1 m1 n1,
  size_qexp (open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q1) = size_qexp q1.
Proof. Admitted.

Hint Resolve size_qexp_open_qexp_wrt_qexp_rec_var : lngen.
Hint Rewrite size_qexp_open_qexp_wrt_qexp_rec_var using solve [auto] : lngen.

(* end hide *)

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

Hint Resolve size_tm_open_tm_wrt_tm_rec_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_tm_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_qexp_rec_var_mutual :
(forall a1 m1 n1,
  size_tm (open_tm_wrt_qexp_rec n1 (q_Var_f m1) a1) = size_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma size_tm_open_tm_wrt_qexp_rec_var :
forall a1 m1 n1,
  size_tm (open_tm_wrt_qexp_rec n1 (q_Var_f m1) a1) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_qexp_rec_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_qexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_qexp_open_qexp_wrt_qexp_var :
forall q1 m1,
  size_qexp (open_qexp_wrt_qexp q1 (q_Var_f m1)) = size_qexp q1.
Proof. Admitted.

Hint Resolve size_qexp_open_qexp_wrt_qexp_var : lngen.
Hint Rewrite size_qexp_open_qexp_wrt_qexp_var using solve [auto] : lngen.

Lemma size_tm_open_tm_wrt_tm_var :
forall a1 x1,
  size_tm (open_tm_wrt_tm a1 (a_Var_f x1)) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_tm_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_tm_var using solve [auto] : lngen.

Lemma size_tm_open_tm_wrt_qexp_var :
forall a1 m1,
  size_tm (open_tm_wrt_qexp a1 (q_Var_f m1)) = size_tm a1.
Proof. Admitted.

Hint Resolve size_tm_open_tm_wrt_qexp_var : lngen.
Hint Rewrite size_tm_open_tm_wrt_qexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_qexp_wrt_qexp_S_mutual :
(forall n1 q1,
  degree_qexp_wrt_qexp n1 q1 ->
  degree_qexp_wrt_qexp (S n1) q1).
Proof. Admitted.

(* end hide *)

Lemma degree_qexp_wrt_qexp_S :
forall n1 q1,
  degree_qexp_wrt_qexp n1 q1 ->
  degree_qexp_wrt_qexp (S n1) q1.
Proof. Admitted.

Hint Resolve degree_qexp_wrt_qexp_S : lngen.

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

Hint Resolve degree_tm_wrt_tm_S : lngen.

(* begin hide *)

Lemma degree_tm_wrt_qexp_S_mutual :
(forall n1 a1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp (S n1) a1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_qexp_S :
forall n1 a1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp (S n1) a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_S : lngen.

Lemma degree_qexp_wrt_qexp_O :
forall n1 q1,
  degree_qexp_wrt_qexp O q1 ->
  degree_qexp_wrt_qexp n1 q1.
Proof. Admitted.

Hint Resolve degree_qexp_wrt_qexp_O : lngen.

Lemma degree_tm_wrt_tm_O :
forall n1 a1,
  degree_tm_wrt_tm O a1 ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_O : lngen.

Lemma degree_tm_wrt_qexp_O :
forall n1 a1,
  degree_tm_wrt_qexp O a1 ->
  degree_tm_wrt_qexp n1 a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_O : lngen.

(* begin hide *)

Lemma degree_qexp_wrt_qexp_close_qexp_wrt_qexp_rec_mutual :
(forall q1 m1 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  degree_qexp_wrt_qexp (S n1) (close_qexp_wrt_qexp_rec n1 m1 q1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_qexp_wrt_qexp_close_qexp_wrt_qexp_rec :
forall q1 m1 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  degree_qexp_wrt_qexp (S n1) (close_qexp_wrt_qexp_rec n1 m1 q1).
Proof. Admitted.

Hint Resolve degree_qexp_wrt_qexp_close_qexp_wrt_qexp_rec : lngen.

(* end hide *)

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

Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_qexp_rec_mutual :
(forall a1 m1 n1 n2,
  degree_tm_wrt_tm n2 a1 ->
  degree_tm_wrt_tm n2 (close_tm_wrt_qexp_rec n1 m1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_qexp_rec :
forall a1 m1 n1 n2,
  degree_tm_wrt_tm n2 a1 ->
  degree_tm_wrt_tm n2 (close_tm_wrt_qexp_rec n1 m1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_close_tm_wrt_qexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_close_tm_wrt_tm_rec_mutual :
(forall a1 x1 n1 n2,
  degree_tm_wrt_qexp n2 a1 ->
  degree_tm_wrt_qexp n2 (close_tm_wrt_tm_rec n1 x1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_close_tm_wrt_tm_rec :
forall a1 x1 n1 n2,
  degree_tm_wrt_qexp n2 a1 ->
  degree_tm_wrt_qexp n2 (close_tm_wrt_tm_rec n1 x1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_close_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_close_tm_wrt_qexp_rec_mutual :
(forall a1 m1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp (S n1) (close_tm_wrt_qexp_rec n1 m1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_close_tm_wrt_qexp_rec :
forall a1 m1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp (S n1) (close_tm_wrt_qexp_rec n1 m1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_close_tm_wrt_qexp_rec : lngen.

(* end hide *)

Lemma degree_qexp_wrt_qexp_close_qexp_wrt_qexp :
forall q1 m1,
  degree_qexp_wrt_qexp 0 q1 ->
  degree_qexp_wrt_qexp 1 (close_qexp_wrt_qexp m1 q1).
Proof. Admitted.

Hint Resolve degree_qexp_wrt_qexp_close_qexp_wrt_qexp : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_tm :
forall a1 x1,
  degree_tm_wrt_tm 0 a1 ->
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_close_tm_wrt_tm : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_qexp :
forall a1 m1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 (close_tm_wrt_qexp m1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_close_tm_wrt_qexp : lngen.

Lemma degree_tm_wrt_qexp_close_tm_wrt_tm :
forall a1 x1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp n1 (close_tm_wrt_tm x1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_close_tm_wrt_tm : lngen.

Lemma degree_tm_wrt_qexp_close_tm_wrt_qexp :
forall a1 m1,
  degree_tm_wrt_qexp 0 a1 ->
  degree_tm_wrt_qexp 1 (close_tm_wrt_qexp m1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_close_tm_wrt_qexp : lngen.

(* begin hide *)

Lemma degree_qexp_wrt_qexp_close_qexp_wrt_qexp_rec_inv_mutual :
(forall q1 m1 n1,
  degree_qexp_wrt_qexp (S n1) (close_qexp_wrt_qexp_rec n1 m1 q1) ->
  degree_qexp_wrt_qexp n1 q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_qexp_wrt_qexp_close_qexp_wrt_qexp_rec_inv :
forall q1 m1 n1,
  degree_qexp_wrt_qexp (S n1) (close_qexp_wrt_qexp_rec n1 m1 q1) ->
  degree_qexp_wrt_qexp n1 q1.
Proof. Admitted.

Hint Immediate degree_qexp_wrt_qexp_close_qexp_wrt_qexp_rec_inv : lngen.

(* end hide *)

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

Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_qexp_rec_inv_mutual :
(forall a1 m1 n1 n2,
  degree_tm_wrt_tm n2 (close_tm_wrt_qexp_rec n1 m1 a1) ->
  degree_tm_wrt_tm n2 a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_close_tm_wrt_qexp_rec_inv :
forall a1 m1 n1 n2,
  degree_tm_wrt_tm n2 (close_tm_wrt_qexp_rec n1 m1 a1) ->
  degree_tm_wrt_tm n2 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_close_tm_wrt_qexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_close_tm_wrt_tm_rec_inv_mutual :
(forall a1 x1 n1 n2,
  degree_tm_wrt_qexp n2 (close_tm_wrt_tm_rec n1 x1 a1) ->
  degree_tm_wrt_qexp n2 a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_close_tm_wrt_tm_rec_inv :
forall a1 x1 n1 n2,
  degree_tm_wrt_qexp n2 (close_tm_wrt_tm_rec n1 x1 a1) ->
  degree_tm_wrt_qexp n2 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_qexp_close_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_close_tm_wrt_qexp_rec_inv_mutual :
(forall a1 m1 n1,
  degree_tm_wrt_qexp (S n1) (close_tm_wrt_qexp_rec n1 m1 a1) ->
  degree_tm_wrt_qexp n1 a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_close_tm_wrt_qexp_rec_inv :
forall a1 m1 n1,
  degree_tm_wrt_qexp (S n1) (close_tm_wrt_qexp_rec n1 m1 a1) ->
  degree_tm_wrt_qexp n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_qexp_close_tm_wrt_qexp_rec_inv : lngen.

(* end hide *)

Lemma degree_qexp_wrt_qexp_close_qexp_wrt_qexp_inv :
forall q1 m1,
  degree_qexp_wrt_qexp 1 (close_qexp_wrt_qexp m1 q1) ->
  degree_qexp_wrt_qexp 0 q1.
Proof. Admitted.

Hint Immediate degree_qexp_wrt_qexp_close_qexp_wrt_qexp_inv : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_tm_inv :
forall a1 x1,
  degree_tm_wrt_tm 1 (close_tm_wrt_tm x1 a1) ->
  degree_tm_wrt_tm 0 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_close_tm_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_tm_close_tm_wrt_qexp_inv :
forall a1 m1 n1,
  degree_tm_wrt_tm n1 (close_tm_wrt_qexp m1 a1) ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_close_tm_wrt_qexp_inv : lngen.

Lemma degree_tm_wrt_qexp_close_tm_wrt_tm_inv :
forall a1 x1 n1,
  degree_tm_wrt_qexp n1 (close_tm_wrt_tm x1 a1) ->
  degree_tm_wrt_qexp n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_qexp_close_tm_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_qexp_close_tm_wrt_qexp_inv :
forall a1 m1,
  degree_tm_wrt_qexp 1 (close_tm_wrt_qexp m1 a1) ->
  degree_tm_wrt_qexp 0 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_qexp_close_tm_wrt_qexp_inv : lngen.

(* begin hide *)

Lemma degree_qexp_wrt_qexp_open_qexp_wrt_qexp_rec_mutual :
(forall q1 q2 n1,
  degree_qexp_wrt_qexp (S n1) q1 ->
  degree_qexp_wrt_qexp n1 q2 ->
  degree_qexp_wrt_qexp n1 (open_qexp_wrt_qexp_rec n1 q2 q1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_qexp_wrt_qexp_open_qexp_wrt_qexp_rec :
forall q1 q2 n1,
  degree_qexp_wrt_qexp (S n1) q1 ->
  degree_qexp_wrt_qexp n1 q2 ->
  degree_qexp_wrt_qexp n1 (open_qexp_wrt_qexp_rec n1 q2 q1).
Proof. Admitted.

Hint Resolve degree_qexp_wrt_qexp_open_qexp_wrt_qexp_rec : lngen.

(* end hide *)

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

Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_qexp_rec_mutual :
(forall a1 q1 n1 n2,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_qexp_rec n2 q1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_qexp_rec :
forall a1 q1 n1 n2,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_qexp_rec n2 q1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_open_tm_wrt_qexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_open_tm_wrt_tm_rec_mutual :
(forall a1 a2 n1 n2,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp n1 a2 ->
  degree_tm_wrt_qexp n1 (open_tm_wrt_tm_rec n2 a2 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_open_tm_wrt_tm_rec :
forall a1 a2 n1 n2,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp n1 a2 ->
  degree_tm_wrt_qexp n1 (open_tm_wrt_tm_rec n2 a2 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_open_tm_wrt_qexp_rec_mutual :
(forall a1 q1 n1,
  degree_tm_wrt_qexp (S n1) a1 ->
  degree_qexp_wrt_qexp n1 q1 ->
  degree_tm_wrt_qexp n1 (open_tm_wrt_qexp_rec n1 q1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_open_tm_wrt_qexp_rec :
forall a1 q1 n1,
  degree_tm_wrt_qexp (S n1) a1 ->
  degree_qexp_wrt_qexp n1 q1 ->
  degree_tm_wrt_qexp n1 (open_tm_wrt_qexp_rec n1 q1 a1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_open_tm_wrt_qexp_rec : lngen.

(* end hide *)

Lemma degree_qexp_wrt_qexp_open_qexp_wrt_qexp :
forall q1 q2,
  degree_qexp_wrt_qexp 1 q1 ->
  degree_qexp_wrt_qexp 0 q2 ->
  degree_qexp_wrt_qexp 0 (open_qexp_wrt_qexp q1 q2).
Proof. Admitted.

Hint Resolve degree_qexp_wrt_qexp_open_qexp_wrt_qexp : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_tm :
forall a1 a2,
  degree_tm_wrt_tm 1 a1 ->
  degree_tm_wrt_tm 0 a2 ->
  degree_tm_wrt_tm 0 (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_qexp :
forall a1 q1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 (open_tm_wrt_qexp a1 q1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_tm_open_tm_wrt_qexp : lngen.

Lemma degree_tm_wrt_qexp_open_tm_wrt_tm :
forall a1 a2 n1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp n1 a2 ->
  degree_tm_wrt_qexp n1 (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_open_tm_wrt_tm : lngen.

Lemma degree_tm_wrt_qexp_open_tm_wrt_qexp :
forall a1 q1,
  degree_tm_wrt_qexp 1 a1 ->
  degree_qexp_wrt_qexp 0 q1 ->
  degree_tm_wrt_qexp 0 (open_tm_wrt_qexp a1 q1).
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_open_tm_wrt_qexp : lngen.

(* begin hide *)

Lemma degree_qexp_wrt_qexp_open_qexp_wrt_qexp_rec_inv_mutual :
(forall q1 q2 n1,
  degree_qexp_wrt_qexp n1 (open_qexp_wrt_qexp_rec n1 q2 q1) ->
  degree_qexp_wrt_qexp (S n1) q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_qexp_wrt_qexp_open_qexp_wrt_qexp_rec_inv :
forall q1 q2 n1,
  degree_qexp_wrt_qexp n1 (open_qexp_wrt_qexp_rec n1 q2 q1) ->
  degree_qexp_wrt_qexp (S n1) q1.
Proof. Admitted.

Hint Immediate degree_qexp_wrt_qexp_open_qexp_wrt_qexp_rec_inv : lngen.

(* end hide *)

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

Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_qexp_rec_inv_mutual :
(forall a1 q1 n1 n2,
  degree_tm_wrt_tm n1 (open_tm_wrt_qexp_rec n2 q1 a1) ->
  degree_tm_wrt_tm n1 a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_tm_open_tm_wrt_qexp_rec_inv :
forall a1 q1 n1 n2,
  degree_tm_wrt_tm n1 (open_tm_wrt_qexp_rec n2 q1 a1) ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_open_tm_wrt_qexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_open_tm_wrt_tm_rec_inv_mutual :
(forall a1 a2 n1 n2,
  degree_tm_wrt_qexp n1 (open_tm_wrt_tm_rec n2 a2 a1) ->
  degree_tm_wrt_qexp n1 a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_open_tm_wrt_tm_rec_inv :
forall a1 a2 n1 n2,
  degree_tm_wrt_qexp n1 (open_tm_wrt_tm_rec n2 a2 a1) ->
  degree_tm_wrt_qexp n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_qexp_open_tm_wrt_tm_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_open_tm_wrt_qexp_rec_inv_mutual :
(forall a1 q1 n1,
  degree_tm_wrt_qexp n1 (open_tm_wrt_qexp_rec n1 q1 a1) ->
  degree_tm_wrt_qexp (S n1) a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma degree_tm_wrt_qexp_open_tm_wrt_qexp_rec_inv :
forall a1 q1 n1,
  degree_tm_wrt_qexp n1 (open_tm_wrt_qexp_rec n1 q1 a1) ->
  degree_tm_wrt_qexp (S n1) a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_qexp_open_tm_wrt_qexp_rec_inv : lngen.

(* end hide *)

Lemma degree_qexp_wrt_qexp_open_qexp_wrt_qexp_inv :
forall q1 q2,
  degree_qexp_wrt_qexp 0 (open_qexp_wrt_qexp q1 q2) ->
  degree_qexp_wrt_qexp 1 q1.
Proof. Admitted.

Hint Immediate degree_qexp_wrt_qexp_open_qexp_wrt_qexp_inv : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_tm_inv :
forall a1 a2,
  degree_tm_wrt_tm 0 (open_tm_wrt_tm a1 a2) ->
  degree_tm_wrt_tm 1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_open_tm_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_tm_open_tm_wrt_qexp_inv :
forall a1 q1 n1,
  degree_tm_wrt_tm n1 (open_tm_wrt_qexp a1 q1) ->
  degree_tm_wrt_tm n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_tm_open_tm_wrt_qexp_inv : lngen.

Lemma degree_tm_wrt_qexp_open_tm_wrt_tm_inv :
forall a1 a2 n1,
  degree_tm_wrt_qexp n1 (open_tm_wrt_tm a1 a2) ->
  degree_tm_wrt_qexp n1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_qexp_open_tm_wrt_tm_inv : lngen.

Lemma degree_tm_wrt_qexp_open_tm_wrt_qexp_inv :
forall a1 q1,
  degree_tm_wrt_qexp 0 (open_tm_wrt_qexp a1 q1) ->
  degree_tm_wrt_qexp 1 a1.
Proof. Admitted.

Hint Immediate degree_tm_wrt_qexp_open_tm_wrt_qexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_qexp_wrt_qexp_rec_inj_mutual :
(forall q1 q2 m1 n1,
  close_qexp_wrt_qexp_rec n1 m1 q1 = close_qexp_wrt_qexp_rec n1 m1 q2 ->
  q1 = q2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_qexp_wrt_qexp_rec_inj :
forall q1 q2 m1 n1,
  close_qexp_wrt_qexp_rec n1 m1 q1 = close_qexp_wrt_qexp_rec n1 m1 q2 ->
  q1 = q2.
Proof. Admitted.

Hint Immediate close_qexp_wrt_qexp_rec_inj : lngen.

(* end hide *)

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

Hint Immediate close_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_qexp_rec_inj_mutual :
(forall a1 a2 m1 n1,
  close_tm_wrt_qexp_rec n1 m1 a1 = close_tm_wrt_qexp_rec n1 m1 a2 ->
  a1 = a2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_qexp_rec_inj :
forall a1 a2 m1 n1,
  close_tm_wrt_qexp_rec n1 m1 a1 = close_tm_wrt_qexp_rec n1 m1 a2 ->
  a1 = a2.
Proof. Admitted.

Hint Immediate close_tm_wrt_qexp_rec_inj : lngen.

(* end hide *)

Lemma close_qexp_wrt_qexp_inj :
forall q1 q2 m1,
  close_qexp_wrt_qexp m1 q1 = close_qexp_wrt_qexp m1 q2 ->
  q1 = q2.
Proof. Admitted.

Hint Immediate close_qexp_wrt_qexp_inj : lngen.

Lemma close_tm_wrt_tm_inj :
forall a1 a2 x1,
  close_tm_wrt_tm x1 a1 = close_tm_wrt_tm x1 a2 ->
  a1 = a2.
Proof. Admitted.

Hint Immediate close_tm_wrt_tm_inj : lngen.

Lemma close_tm_wrt_qexp_inj :
forall a1 a2 m1,
  close_tm_wrt_qexp m1 a1 = close_tm_wrt_qexp m1 a2 ->
  a1 = a2.
Proof. Admitted.

Hint Immediate close_tm_wrt_qexp_inj : lngen.

(* begin hide *)

Lemma close_qexp_wrt_qexp_rec_open_qexp_wrt_qexp_rec_mutual :
(forall q1 m1 n1,
  m1 `notin` fv_q_qexp q1 ->
  close_qexp_wrt_qexp_rec n1 m1 (open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q1) = q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_qexp_wrt_qexp_rec_open_qexp_wrt_qexp_rec :
forall q1 m1 n1,
  m1 `notin` fv_q_qexp q1 ->
  close_qexp_wrt_qexp_rec n1 m1 (open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q1) = q1.
Proof. Admitted.

Hint Resolve close_qexp_wrt_qexp_rec_open_qexp_wrt_qexp_rec : lngen.
Hint Rewrite close_qexp_wrt_qexp_rec_open_qexp_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

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

Hint Resolve close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.
Hint Rewrite close_tm_wrt_tm_rec_open_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec_mutual :
(forall a1 m1 n1,
  m1 `notin` fv_q_tm a1 ->
  close_tm_wrt_qexp_rec n1 m1 (open_tm_wrt_qexp_rec n1 (q_Var_f m1) a1) = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec :
forall a1 m1 n1,
  m1 `notin` fv_q_tm a1 ->
  close_tm_wrt_qexp_rec n1 m1 (open_tm_wrt_qexp_rec n1 (q_Var_f m1) a1) = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec : lngen.
Hint Rewrite close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_qexp_wrt_qexp_open_qexp_wrt_qexp :
forall q1 m1,
  m1 `notin` fv_q_qexp q1 ->
  close_qexp_wrt_qexp m1 (open_qexp_wrt_qexp q1 (q_Var_f m1)) = q1.
Proof. Admitted.

Hint Resolve close_qexp_wrt_qexp_open_qexp_wrt_qexp : lngen.
Hint Rewrite close_qexp_wrt_qexp_open_qexp_wrt_qexp using solve [auto] : lngen.

Lemma close_tm_wrt_tm_open_tm_wrt_tm :
forall a1 x1,
  x1 `notin` fv_tm_tm a1 ->
  close_tm_wrt_tm x1 (open_tm_wrt_tm a1 (a_Var_f x1)) = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_tm_open_tm_wrt_tm : lngen.
Hint Rewrite close_tm_wrt_tm_open_tm_wrt_tm using solve [auto] : lngen.

Lemma close_tm_wrt_qexp_open_tm_wrt_qexp :
forall a1 m1,
  m1 `notin` fv_q_tm a1 ->
  close_tm_wrt_qexp m1 (open_tm_wrt_qexp a1 (q_Var_f m1)) = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_qexp_open_tm_wrt_qexp : lngen.
Hint Rewrite close_tm_wrt_qexp_open_tm_wrt_qexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_qexp_wrt_qexp_rec_close_qexp_wrt_qexp_rec_mutual :
(forall q1 m1 n1,
  open_qexp_wrt_qexp_rec n1 (q_Var_f m1) (close_qexp_wrt_qexp_rec n1 m1 q1) = q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_qexp_wrt_qexp_rec_close_qexp_wrt_qexp_rec :
forall q1 m1 n1,
  open_qexp_wrt_qexp_rec n1 (q_Var_f m1) (close_qexp_wrt_qexp_rec n1 m1 q1) = q1.
Proof. Admitted.

Hint Resolve open_qexp_wrt_qexp_rec_close_qexp_wrt_qexp_rec : lngen.
Hint Rewrite open_qexp_wrt_qexp_rec_close_qexp_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

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

Hint Resolve open_tm_wrt_tm_rec_close_tm_wrt_tm_rec : lngen.
Hint Rewrite open_tm_wrt_tm_rec_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_qexp_rec_close_tm_wrt_qexp_rec_mutual :
(forall a1 m1 n1,
  open_tm_wrt_qexp_rec n1 (q_Var_f m1) (close_tm_wrt_qexp_rec n1 m1 a1) = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_qexp_rec_close_tm_wrt_qexp_rec :
forall a1 m1 n1,
  open_tm_wrt_qexp_rec n1 (q_Var_f m1) (close_tm_wrt_qexp_rec n1 m1 a1) = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_qexp_rec_close_tm_wrt_qexp_rec : lngen.
Hint Rewrite open_tm_wrt_qexp_rec_close_tm_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_qexp_wrt_qexp_close_qexp_wrt_qexp :
forall q1 m1,
  open_qexp_wrt_qexp (close_qexp_wrt_qexp m1 q1) (q_Var_f m1) = q1.
Proof. Admitted.

Hint Resolve open_qexp_wrt_qexp_close_qexp_wrt_qexp : lngen.
Hint Rewrite open_qexp_wrt_qexp_close_qexp_wrt_qexp using solve [auto] : lngen.

Lemma open_tm_wrt_tm_close_tm_wrt_tm :
forall a1 x1,
  open_tm_wrt_tm (close_tm_wrt_tm x1 a1) (a_Var_f x1) = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_tm_close_tm_wrt_tm : lngen.
Hint Rewrite open_tm_wrt_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma open_tm_wrt_qexp_close_tm_wrt_qexp :
forall a1 m1,
  open_tm_wrt_qexp (close_tm_wrt_qexp m1 a1) (q_Var_f m1) = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_qexp_close_tm_wrt_qexp : lngen.
Hint Rewrite open_tm_wrt_qexp_close_tm_wrt_qexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_qexp_wrt_qexp_rec_inj_mutual :
(forall q2 q1 m1 n1,
  m1 `notin` fv_q_qexp q2 ->
  m1 `notin` fv_q_qexp q1 ->
  open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q2 = open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q1 ->
  q2 = q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_qexp_wrt_qexp_rec_inj :
forall q2 q1 m1 n1,
  m1 `notin` fv_q_qexp q2 ->
  m1 `notin` fv_q_qexp q1 ->
  open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q2 = open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q1 ->
  q2 = q1.
Proof. Admitted.

Hint Immediate open_qexp_wrt_qexp_rec_inj : lngen.

(* end hide *)

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

Hint Immediate open_tm_wrt_tm_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_qexp_rec_inj_mutual :
(forall a2 a1 m1 n1,
  m1 `notin` fv_q_tm a2 ->
  m1 `notin` fv_q_tm a1 ->
  open_tm_wrt_qexp_rec n1 (q_Var_f m1) a2 = open_tm_wrt_qexp_rec n1 (q_Var_f m1) a1 ->
  a2 = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_qexp_rec_inj :
forall a2 a1 m1 n1,
  m1 `notin` fv_q_tm a2 ->
  m1 `notin` fv_q_tm a1 ->
  open_tm_wrt_qexp_rec n1 (q_Var_f m1) a2 = open_tm_wrt_qexp_rec n1 (q_Var_f m1) a1 ->
  a2 = a1.
Proof. Admitted.

Hint Immediate open_tm_wrt_qexp_rec_inj : lngen.

(* end hide *)

Lemma open_qexp_wrt_qexp_inj :
forall q2 q1 m1,
  m1 `notin` fv_q_qexp q2 ->
  m1 `notin` fv_q_qexp q1 ->
  open_qexp_wrt_qexp q2 (q_Var_f m1) = open_qexp_wrt_qexp q1 (q_Var_f m1) ->
  q2 = q1.
Proof. Admitted.

Hint Immediate open_qexp_wrt_qexp_inj : lngen.

Lemma open_tm_wrt_tm_inj :
forall a2 a1 x1,
  x1 `notin` fv_tm_tm a2 ->
  x1 `notin` fv_tm_tm a1 ->
  open_tm_wrt_tm a2 (a_Var_f x1) = open_tm_wrt_tm a1 (a_Var_f x1) ->
  a2 = a1.
Proof. Admitted.

Hint Immediate open_tm_wrt_tm_inj : lngen.

Lemma open_tm_wrt_qexp_inj :
forall a2 a1 m1,
  m1 `notin` fv_q_tm a2 ->
  m1 `notin` fv_q_tm a1 ->
  open_tm_wrt_qexp a2 (q_Var_f m1) = open_tm_wrt_qexp a1 (q_Var_f m1) ->
  a2 = a1.
Proof. Admitted.

Hint Immediate open_tm_wrt_qexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_qexp_wrt_qexp_of_lc_qexp_mutual :
(forall q1,
  lc_qexp q1 ->
  degree_qexp_wrt_qexp 0 q1).
Proof. Admitted.

(* end hide *)

Lemma degree_qexp_wrt_qexp_of_lc_qexp :
forall q1,
  lc_qexp q1 ->
  degree_qexp_wrt_qexp 0 q1.
Proof. Admitted.

Hint Resolve degree_qexp_wrt_qexp_of_lc_qexp : lngen.

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

Hint Resolve degree_tm_wrt_tm_of_lc_tm : lngen.

(* begin hide *)

Lemma degree_tm_wrt_qexp_of_lc_tm_mutual :
(forall a1,
  lc_tm a1 ->
  degree_tm_wrt_qexp 0 a1).
Proof. Admitted.

(* end hide *)

Lemma degree_tm_wrt_qexp_of_lc_tm :
forall a1,
  lc_tm a1 ->
  degree_tm_wrt_qexp 0 a1.
Proof. Admitted.

Hint Resolve degree_tm_wrt_qexp_of_lc_tm : lngen.

(* begin hide *)

Lemma lc_qexp_of_degree_size_mutual :
forall i1,
(forall q1,
  size_qexp q1 = i1 ->
  degree_qexp_wrt_qexp 0 q1 ->
  lc_qexp q1).
Proof. Admitted.

(* end hide *)

Lemma lc_qexp_of_degree :
forall q1,
  degree_qexp_wrt_qexp 0 q1 ->
  lc_qexp q1.
Proof. Admitted.

Hint Resolve lc_qexp_of_degree : lngen.

(* begin hide *)

Lemma lc_tm_of_degree_size_mutual :
forall i1,
(forall a1,
  size_tm a1 = i1 ->
  degree_tm_wrt_tm 0 a1 ->
  degree_tm_wrt_qexp 0 a1 ->
  lc_tm a1).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_of_degree :
forall a1,
  degree_tm_wrt_tm 0 a1 ->
  degree_tm_wrt_qexp 0 a1 ->
  lc_tm a1.
Proof. Admitted.

Hint Resolve lc_tm_of_degree : lngen.

Ltac qexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_qexp_wrt_qexp_of_lc_qexp in J1; clear H
          end).

Ltac tm_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_tm_wrt_tm_of_lc_tm in J1;
              let J2 := fresh in pose proof H as J2; apply degree_tm_wrt_qexp_of_lc_tm in J2; clear H
          end).

Lemma lc_a_Pi_exists :
forall x1 q1 A1 B1,
  lc_qexp q1 ->
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm B1 (a_Var_f x1)) ->
  lc_tm (a_Pi q1 A1 B1).
Proof. Admitted.

Lemma lc_a_Lam_exists :
forall x1 q1 A1 a1,
  lc_qexp q1 ->
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm a1 (a_Var_f x1)) ->
  lc_tm (a_Lam q1 A1 a1).
Proof. Admitted.

Lemma lc_a_LetBoxB_exists :
forall x1 a1 b1 B1,
  lc_tm a1 ->
  lc_tm (open_tm_wrt_tm b1 (a_Var_f x1)) ->
  lc_tm B1 ->
  lc_tm (a_LetBoxB a1 b1 B1).
Proof. Admitted.

Lemma lc_a_Let_exists :
forall x1 a1 b1,
  lc_tm a1 ->
  lc_tm (open_tm_wrt_tm b1 (a_Var_f x1)) ->
  lc_tm (a_Let a1 b1).
Proof. Admitted.

Lemma lc_a_Sigma_exists :
forall x1 q1 A1 B1,
  lc_qexp q1 ->
  lc_tm A1 ->
  lc_tm (open_tm_wrt_tm B1 (a_Var_f x1)) ->
  lc_tm (a_Sigma q1 A1 B1).
Proof. Admitted.

Lemma lc_a_Spread_exists :
forall x1 a1 b1 B1,
  lc_tm a1 ->
  lc_tm (open_tm_wrt_tm b1 (a_Var_f x1)) ->
  lc_tm B1 ->
  lc_tm (a_Spread a1 b1 B1).
Proof. Admitted.

Lemma lc_a_AllU_exists :
forall m1 A1,
  lc_tm (open_tm_wrt_qexp A1 (q_Var_f m1)) ->
  lc_tm (a_AllU A1).
Proof. Admitted.

Lemma lc_a_LamU_exists :
forall m1 a1,
  lc_tm (open_tm_wrt_qexp a1 (q_Var_f m1)) ->
  lc_tm (a_LamU a1).
Proof. Admitted.

Hint Extern 1 (lc_tm (a_Pi _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Pi_exists x1) : core.

Hint Extern 1 (lc_tm (a_Lam _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Lam_exists x1) : core.

Hint Extern 1 (lc_tm (a_LetBoxB _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_LetBoxB_exists x1) : core.

Hint Extern 1 (lc_tm (a_Let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Let_exists x1) : core.

Hint Extern 1 (lc_tm (a_Sigma _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Sigma_exists x1) : core.

Hint Extern 1 (lc_tm (a_Spread _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_Spread_exists x1) : core.

Hint Extern 1 (lc_tm (a_AllU _)) =>
  let m1 := fresh in
  pick_fresh m1;
  apply (lc_a_AllU_exists m1) : core.

Hint Extern 1 (lc_tm (a_LamU _)) =>
  let m1 := fresh in
  pick_fresh m1;
  apply (lc_a_LamU_exists m1) : core.

Lemma lc_body_qexp_wrt_qexp :
forall q1 q2,
  body_qexp_wrt_qexp q1 ->
  lc_qexp q2 ->
  lc_qexp (open_qexp_wrt_qexp q1 q2).
Proof. Admitted.

Hint Resolve lc_body_qexp_wrt_qexp : lngen.

Lemma lc_body_tm_wrt_tm :
forall a1 a2,
  body_tm_wrt_tm a1 ->
  lc_tm a2 ->
  lc_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve lc_body_tm_wrt_tm : lngen.

Lemma lc_body_tm_wrt_qexp :
forall a1 q1,
  body_tm_wrt_qexp a1 ->
  lc_qexp q1 ->
  lc_tm (open_tm_wrt_qexp a1 q1).
Proof. Admitted.

Hint Resolve lc_body_tm_wrt_qexp : lngen.

Lemma lc_body_a_Pi_3 :
forall q1 A1 B1,
  lc_tm (a_Pi q1 A1 B1) ->
  body_tm_wrt_tm B1.
Proof. Admitted.

Hint Resolve lc_body_a_Pi_3 : lngen.

Lemma lc_body_a_Lam_3 :
forall q1 A1 a1,
  lc_tm (a_Lam q1 A1 a1) ->
  body_tm_wrt_tm a1.
Proof. Admitted.

Hint Resolve lc_body_a_Lam_3 : lngen.

Lemma lc_body_a_LetBoxB_2 :
forall a1 b1 B1,
  lc_tm (a_LetBoxB a1 b1 B1) ->
  body_tm_wrt_tm b1.
Proof. Admitted.

Hint Resolve lc_body_a_LetBoxB_2 : lngen.

Lemma lc_body_a_Let_2 :
forall a1 b1,
  lc_tm (a_Let a1 b1) ->
  body_tm_wrt_tm b1.
Proof. Admitted.

Hint Resolve lc_body_a_Let_2 : lngen.

Lemma lc_body_a_Sigma_3 :
forall q1 A1 B1,
  lc_tm (a_Sigma q1 A1 B1) ->
  body_tm_wrt_tm B1.
Proof. Admitted.

Hint Resolve lc_body_a_Sigma_3 : lngen.

Lemma lc_body_a_Spread_2 :
forall a1 b1 B1,
  lc_tm (a_Spread a1 b1 B1) ->
  body_tm_wrt_tm b1.
Proof. Admitted.

Hint Resolve lc_body_a_Spread_2 : lngen.

Lemma lc_body_a_AllU_1 :
forall A1,
  lc_tm (a_AllU A1) ->
  body_tm_wrt_qexp A1.
Proof. Admitted.

Hint Resolve lc_body_a_AllU_1 : lngen.

Lemma lc_body_a_LamU_1 :
forall a1,
  lc_tm (a_LamU a1) ->
  body_tm_wrt_qexp a1.
Proof. Admitted.

Hint Resolve lc_body_a_LamU_1 : lngen.

(* begin hide *)

Lemma lc_qexp_unique_mutual :
(forall q1 (proof2 proof3 : lc_qexp q1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_qexp_unique :
forall q1 (proof2 proof3 : lc_qexp q1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_qexp_unique : lngen.

(* begin hide *)

Lemma lc_tm_unique_mutual :
(forall a1 (proof2 proof3 : lc_tm a1), proof2 = proof3).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_unique :
forall a1 (proof2 proof3 : lc_tm a1), proof2 = proof3.
Proof. Admitted.

Hint Resolve lc_tm_unique : lngen.

(* begin hide *)

Lemma lc_qexp_of_lc_set_qexp_mutual :
(forall q1, lc_set_qexp q1 -> lc_qexp q1).
Proof. Admitted.

(* end hide *)

Lemma lc_qexp_of_lc_set_qexp :
forall q1, lc_set_qexp q1 -> lc_qexp q1.
Proof. Admitted.

Hint Resolve lc_qexp_of_lc_set_qexp : lngen.

(* begin hide *)

Lemma lc_tm_of_lc_set_tm_mutual :
(forall a1, lc_set_tm a1 -> lc_tm a1).
Proof. Admitted.

(* end hide *)

Lemma lc_tm_of_lc_set_tm :
forall a1, lc_set_tm a1 -> lc_tm a1.
Proof. Admitted.

Hint Resolve lc_tm_of_lc_set_tm : lngen.

(* begin hide *)

Lemma lc_set_qexp_of_lc_qexp_size_mutual :
forall i1,
(forall q1,
  size_qexp q1 = i1 ->
  lc_qexp q1 ->
  lc_set_qexp q1).
Proof. Admitted.

(* end hide *)

Lemma lc_set_qexp_of_lc_qexp :
forall q1,
  lc_qexp q1 ->
  lc_set_qexp q1.
Proof. Admitted.

Hint Resolve lc_set_qexp_of_lc_qexp : lngen.

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

Hint Resolve lc_set_tm_of_lc_tm : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_qexp_wrt_qexp_rec_degree_qexp_wrt_qexp_mutual :
(forall q1 m1 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  m1 `notin` fv_q_qexp q1 ->
  close_qexp_wrt_qexp_rec n1 m1 q1 = q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_qexp_wrt_qexp_rec_degree_qexp_wrt_qexp :
forall q1 m1 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  m1 `notin` fv_q_qexp q1 ->
  close_qexp_wrt_qexp_rec n1 m1 q1 = q1.
Proof. Admitted.

Hint Resolve close_qexp_wrt_qexp_rec_degree_qexp_wrt_qexp : lngen.
Hint Rewrite close_qexp_wrt_qexp_rec_degree_qexp_wrt_qexp using solve [auto] : lngen.

(* end hide *)

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

Hint Resolve close_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
Hint Rewrite close_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_qexp_rec_degree_tm_wrt_qexp_mutual :
(forall a1 m1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  m1 `notin` fv_q_tm a1 ->
  close_tm_wrt_qexp_rec n1 m1 a1 = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma close_tm_wrt_qexp_rec_degree_tm_wrt_qexp :
forall a1 m1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  m1 `notin` fv_q_tm a1 ->
  close_tm_wrt_qexp_rec n1 m1 a1 = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_qexp_rec_degree_tm_wrt_qexp : lngen.
Hint Rewrite close_tm_wrt_qexp_rec_degree_tm_wrt_qexp using solve [auto] : lngen.

(* end hide *)

Lemma close_qexp_wrt_qexp_lc_qexp :
forall q1 m1,
  lc_qexp q1 ->
  m1 `notin` fv_q_qexp q1 ->
  close_qexp_wrt_qexp m1 q1 = q1.
Proof. Admitted.

Hint Resolve close_qexp_wrt_qexp_lc_qexp : lngen.
Hint Rewrite close_qexp_wrt_qexp_lc_qexp using solve [auto] : lngen.

Lemma close_tm_wrt_tm_lc_tm :
forall a1 x1,
  lc_tm a1 ->
  x1 `notin` fv_tm_tm a1 ->
  close_tm_wrt_tm x1 a1 = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_tm_lc_tm : lngen.
Hint Rewrite close_tm_wrt_tm_lc_tm using solve [auto] : lngen.

Lemma close_tm_wrt_qexp_lc_tm :
forall a1 m1,
  lc_tm a1 ->
  m1 `notin` fv_q_tm a1 ->
  close_tm_wrt_qexp m1 a1 = a1.
Proof. Admitted.

Hint Resolve close_tm_wrt_qexp_lc_tm : lngen.
Hint Rewrite close_tm_wrt_qexp_lc_tm using solve [auto] : lngen.

(* begin hide *)

Lemma open_qexp_wrt_qexp_rec_degree_qexp_wrt_qexp_mutual :
(forall q2 q1 n1,
  degree_qexp_wrt_qexp n1 q2 ->
  open_qexp_wrt_qexp_rec n1 q1 q2 = q2).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_qexp_wrt_qexp_rec_degree_qexp_wrt_qexp :
forall q2 q1 n1,
  degree_qexp_wrt_qexp n1 q2 ->
  open_qexp_wrt_qexp_rec n1 q1 q2 = q2.
Proof. Admitted.

Hint Resolve open_qexp_wrt_qexp_rec_degree_qexp_wrt_qexp : lngen.
Hint Rewrite open_qexp_wrt_qexp_rec_degree_qexp_wrt_qexp using solve [auto] : lngen.

(* end hide *)

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

Hint Resolve open_tm_wrt_tm_rec_degree_tm_wrt_tm : lngen.
Hint Rewrite open_tm_wrt_tm_rec_degree_tm_wrt_tm using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_qexp_rec_degree_tm_wrt_qexp_mutual :
(forall a1 q1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  open_tm_wrt_qexp_rec n1 q1 a1 = a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma open_tm_wrt_qexp_rec_degree_tm_wrt_qexp :
forall a1 q1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  open_tm_wrt_qexp_rec n1 q1 a1 = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_qexp_rec_degree_tm_wrt_qexp : lngen.
Hint Rewrite open_tm_wrt_qexp_rec_degree_tm_wrt_qexp using solve [auto] : lngen.

(* end hide *)

Lemma open_qexp_wrt_qexp_lc_qexp :
forall q2 q1,
  lc_qexp q2 ->
  open_qexp_wrt_qexp q2 q1 = q2.
Proof. Admitted.

Hint Resolve open_qexp_wrt_qexp_lc_qexp : lngen.
Hint Rewrite open_qexp_wrt_qexp_lc_qexp using solve [auto] : lngen.

Lemma open_tm_wrt_tm_lc_tm :
forall a2 a1,
  lc_tm a2 ->
  open_tm_wrt_tm a2 a1 = a2.
Proof. Admitted.

Hint Resolve open_tm_wrt_tm_lc_tm : lngen.
Hint Rewrite open_tm_wrt_tm_lc_tm using solve [auto] : lngen.

Lemma open_tm_wrt_qexp_lc_tm :
forall a1 q1,
  lc_tm a1 ->
  open_tm_wrt_qexp a1 q1 = a1.
Proof. Admitted.

Hint Resolve open_tm_wrt_qexp_lc_tm : lngen.
Hint Rewrite open_tm_wrt_qexp_lc_tm using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_q_qexp_close_qexp_wrt_qexp_rec_mutual :
(forall q1 m1 n1,
  fv_q_qexp (close_qexp_wrt_qexp_rec n1 m1 q1) [=] remove m1 (fv_q_qexp q1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_qexp_close_qexp_wrt_qexp_rec :
forall q1 m1 n1,
  fv_q_qexp (close_qexp_wrt_qexp_rec n1 m1 q1) [=] remove m1 (fv_q_qexp q1).
Proof. Admitted.

Hint Resolve fv_q_qexp_close_qexp_wrt_qexp_rec : lngen.
Hint Rewrite fv_q_qexp_close_qexp_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

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

Hint Resolve fv_tm_tm_close_tm_wrt_tm_rec : lngen.
Hint Rewrite fv_tm_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_close_tm_wrt_qexp_rec_mutual :
(forall a1 m1 n1,
  fv_tm_tm (close_tm_wrt_qexp_rec n1 m1 a1) [=] fv_tm_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_close_tm_wrt_qexp_rec :
forall a1 m1 n1,
  fv_tm_tm (close_tm_wrt_qexp_rec n1 m1 a1) [=] fv_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_close_tm_wrt_qexp_rec : lngen.
Hint Rewrite fv_tm_tm_close_tm_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_close_tm_wrt_tm_rec_mutual :
(forall a1 x1 n1,
  fv_q_tm (close_tm_wrt_tm_rec n1 x1 a1) [=] fv_q_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_close_tm_wrt_tm_rec :
forall a1 x1 n1,
  fv_q_tm (close_tm_wrt_tm_rec n1 x1 a1) [=] fv_q_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_close_tm_wrt_tm_rec : lngen.
Hint Rewrite fv_q_tm_close_tm_wrt_tm_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_close_tm_wrt_qexp_rec_mutual :
(forall a1 m1 n1,
  fv_q_tm (close_tm_wrt_qexp_rec n1 m1 a1) [=] remove m1 (fv_q_tm a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_close_tm_wrt_qexp_rec :
forall a1 m1 n1,
  fv_q_tm (close_tm_wrt_qexp_rec n1 m1 a1) [=] remove m1 (fv_q_tm a1).
Proof. Admitted.

Hint Resolve fv_q_tm_close_tm_wrt_qexp_rec : lngen.
Hint Rewrite fv_q_tm_close_tm_wrt_qexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_q_qexp_close_qexp_wrt_qexp :
forall q1 m1,
  fv_q_qexp (close_qexp_wrt_qexp m1 q1) [=] remove m1 (fv_q_qexp q1).
Proof. Admitted.

Hint Resolve fv_q_qexp_close_qexp_wrt_qexp : lngen.
Hint Rewrite fv_q_qexp_close_qexp_wrt_qexp using solve [auto] : lngen.

Lemma fv_tm_tm_close_tm_wrt_tm :
forall a1 x1,
  fv_tm_tm (close_tm_wrt_tm x1 a1) [=] remove x1 (fv_tm_tm a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_close_tm_wrt_tm : lngen.
Hint Rewrite fv_tm_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma fv_tm_tm_close_tm_wrt_qexp :
forall a1 m1,
  fv_tm_tm (close_tm_wrt_qexp m1 a1) [=] fv_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_close_tm_wrt_qexp : lngen.
Hint Rewrite fv_tm_tm_close_tm_wrt_qexp using solve [auto] : lngen.

Lemma fv_q_tm_close_tm_wrt_tm :
forall a1 x1,
  fv_q_tm (close_tm_wrt_tm x1 a1) [=] fv_q_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_close_tm_wrt_tm : lngen.
Hint Rewrite fv_q_tm_close_tm_wrt_tm using solve [auto] : lngen.

Lemma fv_q_tm_close_tm_wrt_qexp :
forall a1 m1,
  fv_q_tm (close_tm_wrt_qexp m1 a1) [=] remove m1 (fv_q_tm a1).
Proof. Admitted.

Hint Resolve fv_q_tm_close_tm_wrt_qexp : lngen.
Hint Rewrite fv_q_tm_close_tm_wrt_qexp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_q_qexp_open_qexp_wrt_qexp_rec_lower_mutual :
(forall q1 q2 n1,
  fv_q_qexp q1 [<=] fv_q_qexp (open_qexp_wrt_qexp_rec n1 q2 q1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_qexp_open_qexp_wrt_qexp_rec_lower :
forall q1 q2 n1,
  fv_q_qexp q1 [<=] fv_q_qexp (open_qexp_wrt_qexp_rec n1 q2 q1).
Proof. Admitted.

Hint Resolve fv_q_qexp_open_qexp_wrt_qexp_rec_lower : lngen.

(* end hide *)

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

Hint Resolve fv_tm_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_open_tm_wrt_qexp_rec_lower_mutual :
(forall a1 q1 n1,
  fv_tm_tm a1 [<=] fv_tm_tm (open_tm_wrt_qexp_rec n1 q1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_open_tm_wrt_qexp_rec_lower :
forall a1 q1 n1,
  fv_tm_tm a1 [<=] fv_tm_tm (open_tm_wrt_qexp_rec n1 q1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_open_tm_wrt_qexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_open_tm_wrt_tm_rec_lower_mutual :
(forall a1 a2 n1,
  fv_q_tm a1 [<=] fv_q_tm (open_tm_wrt_tm_rec n1 a2 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_open_tm_wrt_tm_rec_lower :
forall a1 a2 n1,
  fv_q_tm a1 [<=] fv_q_tm (open_tm_wrt_tm_rec n1 a2 a1).
Proof. Admitted.

Hint Resolve fv_q_tm_open_tm_wrt_tm_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_open_tm_wrt_qexp_rec_lower_mutual :
(forall a1 q1 n1,
  fv_q_tm a1 [<=] fv_q_tm (open_tm_wrt_qexp_rec n1 q1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_open_tm_wrt_qexp_rec_lower :
forall a1 q1 n1,
  fv_q_tm a1 [<=] fv_q_tm (open_tm_wrt_qexp_rec n1 q1 a1).
Proof. Admitted.

Hint Resolve fv_q_tm_open_tm_wrt_qexp_rec_lower : lngen.

(* end hide *)

Lemma fv_q_qexp_open_qexp_wrt_qexp_lower :
forall q1 q2,
  fv_q_qexp q1 [<=] fv_q_qexp (open_qexp_wrt_qexp q1 q2).
Proof. Admitted.

Hint Resolve fv_q_qexp_open_qexp_wrt_qexp_lower : lngen.

Lemma fv_tm_tm_open_tm_wrt_tm_lower :
forall a1 a2,
  fv_tm_tm a1 [<=] fv_tm_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve fv_tm_tm_open_tm_wrt_tm_lower : lngen.

Lemma fv_tm_tm_open_tm_wrt_qexp_lower :
forall a1 q1,
  fv_tm_tm a1 [<=] fv_tm_tm (open_tm_wrt_qexp a1 q1).
Proof. Admitted.

Hint Resolve fv_tm_tm_open_tm_wrt_qexp_lower : lngen.

Lemma fv_q_tm_open_tm_wrt_tm_lower :
forall a1 a2,
  fv_q_tm a1 [<=] fv_q_tm (open_tm_wrt_tm a1 a2).
Proof. Admitted.

Hint Resolve fv_q_tm_open_tm_wrt_tm_lower : lngen.

Lemma fv_q_tm_open_tm_wrt_qexp_lower :
forall a1 q1,
  fv_q_tm a1 [<=] fv_q_tm (open_tm_wrt_qexp a1 q1).
Proof. Admitted.

Hint Resolve fv_q_tm_open_tm_wrt_qexp_lower : lngen.

(* begin hide *)

Lemma fv_q_qexp_open_qexp_wrt_qexp_rec_upper_mutual :
(forall q1 q2 n1,
  fv_q_qexp (open_qexp_wrt_qexp_rec n1 q2 q1) [<=] fv_q_qexp q2 `union` fv_q_qexp q1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_qexp_open_qexp_wrt_qexp_rec_upper :
forall q1 q2 n1,
  fv_q_qexp (open_qexp_wrt_qexp_rec n1 q2 q1) [<=] fv_q_qexp q2 `union` fv_q_qexp q1.
Proof. Admitted.

Hint Resolve fv_q_qexp_open_qexp_wrt_qexp_rec_upper : lngen.

(* end hide *)

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

Hint Resolve fv_tm_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_open_tm_wrt_qexp_rec_upper_mutual :
(forall a1 q1 n1,
  fv_tm_tm (open_tm_wrt_qexp_rec n1 q1 a1) [<=] fv_tm_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_tm_tm_open_tm_wrt_qexp_rec_upper :
forall a1 q1 n1,
  fv_tm_tm (open_tm_wrt_qexp_rec n1 q1 a1) [<=] fv_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_open_tm_wrt_qexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_open_tm_wrt_tm_rec_upper_mutual :
(forall a1 a2 n1,
  fv_q_tm (open_tm_wrt_tm_rec n1 a2 a1) [<=] fv_q_tm a2 `union` fv_q_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_open_tm_wrt_tm_rec_upper :
forall a1 a2 n1,
  fv_q_tm (open_tm_wrt_tm_rec n1 a2 a1) [<=] fv_q_tm a2 `union` fv_q_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_open_tm_wrt_tm_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_open_tm_wrt_qexp_rec_upper_mutual :
(forall a1 q1 n1,
  fv_q_tm (open_tm_wrt_qexp_rec n1 q1 a1) [<=] fv_q_qexp q1 `union` fv_q_tm a1).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma fv_q_tm_open_tm_wrt_qexp_rec_upper :
forall a1 q1 n1,
  fv_q_tm (open_tm_wrt_qexp_rec n1 q1 a1) [<=] fv_q_qexp q1 `union` fv_q_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_open_tm_wrt_qexp_rec_upper : lngen.

(* end hide *)

Lemma fv_q_qexp_open_qexp_wrt_qexp_upper :
forall q1 q2,
  fv_q_qexp (open_qexp_wrt_qexp q1 q2) [<=] fv_q_qexp q2 `union` fv_q_qexp q1.
Proof. Admitted.

Hint Resolve fv_q_qexp_open_qexp_wrt_qexp_upper : lngen.

Lemma fv_tm_tm_open_tm_wrt_tm_upper :
forall a1 a2,
  fv_tm_tm (open_tm_wrt_tm a1 a2) [<=] fv_tm_tm a2 `union` fv_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_open_tm_wrt_tm_upper : lngen.

Lemma fv_tm_tm_open_tm_wrt_qexp_upper :
forall a1 q1,
  fv_tm_tm (open_tm_wrt_qexp a1 q1) [<=] fv_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_open_tm_wrt_qexp_upper : lngen.

Lemma fv_q_tm_open_tm_wrt_tm_upper :
forall a1 a2,
  fv_q_tm (open_tm_wrt_tm a1 a2) [<=] fv_q_tm a2 `union` fv_q_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_open_tm_wrt_tm_upper : lngen.

Lemma fv_q_tm_open_tm_wrt_qexp_upper :
forall a1 q1,
  fv_q_tm (open_tm_wrt_qexp a1 q1) [<=] fv_q_qexp q1 `union` fv_q_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_open_tm_wrt_qexp_upper : lngen.

(* begin hide *)

Lemma fv_q_qexp_subst_q_qexp_fresh_mutual :
(forall q1 q2 m1,
  m1 `notin` fv_q_qexp q1 ->
  fv_q_qexp (subst_q_qexp q2 m1 q1) [=] fv_q_qexp q1).
Proof. Admitted.

(* end hide *)

Lemma fv_q_qexp_subst_q_qexp_fresh :
forall q1 q2 m1,
  m1 `notin` fv_q_qexp q1 ->
  fv_q_qexp (subst_q_qexp q2 m1 q1) [=] fv_q_qexp q1.
Proof. Admitted.

Hint Resolve fv_q_qexp_subst_q_qexp_fresh : lngen.
Hint Rewrite fv_q_qexp_subst_q_qexp_fresh using solve [auto] : lngen.

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

Hint Resolve fv_tm_tm_subst_tm_tm_fresh : lngen.
Hint Rewrite fv_tm_tm_subst_tm_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_q_tm_subst_tm_tm_fresh_mutual :
(forall a1 q1 m1,
  fv_tm_tm (subst_q_tm q1 m1 a1) [=] fv_tm_tm a1).
Proof. Admitted.

(* end hide *)

Lemma fv_q_tm_subst_tm_tm_fresh :
forall a1 q1 m1,
  fv_tm_tm (subst_q_tm q1 m1 a1) [=] fv_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_subst_tm_tm_fresh : lngen.
Hint Rewrite fv_q_tm_subst_tm_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_q_tm_subst_q_tm_fresh_mutual :
(forall a1 q1 m1,
  m1 `notin` fv_q_tm a1 ->
  fv_q_tm (subst_q_tm q1 m1 a1) [=] fv_q_tm a1).
Proof. Admitted.

(* end hide *)

Lemma fv_q_tm_subst_q_tm_fresh :
forall a1 q1 m1,
  m1 `notin` fv_q_tm a1 ->
  fv_q_tm (subst_q_tm q1 m1 a1) [=] fv_q_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_subst_q_tm_fresh : lngen.
Hint Rewrite fv_q_tm_subst_q_tm_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_q_qexp_subst_q_qexp_lower_mutual :
(forall q1 q2 m1,
  remove m1 (fv_q_qexp q1) [<=] fv_q_qexp (subst_q_qexp q2 m1 q1)).
Proof. Admitted.

(* end hide *)

Lemma fv_q_qexp_subst_q_qexp_lower :
forall q1 q2 m1,
  remove m1 (fv_q_qexp q1) [<=] fv_q_qexp (subst_q_qexp q2 m1 q1).
Proof. Admitted.

Hint Resolve fv_q_qexp_subst_q_qexp_lower : lngen.

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

Hint Resolve fv_tm_tm_subst_tm_tm_lower : lngen.

(* begin hide *)

Lemma fv_tm_tm_subst_q_tm_lower_mutual :
(forall a1 q1 m1,
  fv_tm_tm a1 [<=] fv_tm_tm (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_subst_q_tm_lower :
forall a1 q1 m1,
  fv_tm_tm a1 [<=] fv_tm_tm (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_subst_q_tm_lower : lngen.

(* begin hide *)

Lemma fv_q_tm_subst_tm_tm_lower_mutual :
(forall a1 a2 x1,
  fv_q_tm a1 [<=] fv_q_tm (subst_tm_tm a2 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_q_tm_subst_tm_tm_lower :
forall a1 a2 x1,
  fv_q_tm a1 [<=] fv_q_tm (subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve fv_q_tm_subst_tm_tm_lower : lngen.

(* begin hide *)

Lemma fv_q_tm_subst_q_tm_lower_mutual :
(forall a1 q1 m1,
  remove m1 (fv_q_tm a1) [<=] fv_q_tm (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_q_tm_subst_q_tm_lower :
forall a1 q1 m1,
  remove m1 (fv_q_tm a1) [<=] fv_q_tm (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve fv_q_tm_subst_q_tm_lower : lngen.

(* begin hide *)

Lemma fv_q_qexp_subst_q_qexp_notin_mutual :
(forall q1 q2 m1 m2,
  m2 `notin` fv_q_qexp q1 ->
  m2 `notin` fv_q_qexp q2 ->
  m2 `notin` fv_q_qexp (subst_q_qexp q2 m1 q1)).
Proof. Admitted.

(* end hide *)

Lemma fv_q_qexp_subst_q_qexp_notin :
forall q1 q2 m1 m2,
  m2 `notin` fv_q_qexp q1 ->
  m2 `notin` fv_q_qexp q2 ->
  m2 `notin` fv_q_qexp (subst_q_qexp q2 m1 q1).
Proof. Admitted.

Hint Resolve fv_q_qexp_subst_q_qexp_notin : lngen.

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

Hint Resolve fv_tm_tm_subst_tm_tm_notin : lngen.

(* begin hide *)

Lemma fv_tm_tm_subst_q_tm_notin_mutual :
(forall a1 q1 m1 x1,
  x1 `notin` fv_tm_tm a1 ->
  x1 `notin` fv_tm_tm (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_subst_q_tm_notin :
forall a1 q1 m1 x1,
  x1 `notin` fv_tm_tm a1 ->
  x1 `notin` fv_tm_tm (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve fv_tm_tm_subst_q_tm_notin : lngen.

(* begin hide *)

Lemma fv_q_tm_subst_tm_tm_notin_mutual :
(forall a1 a2 x1 m1,
  m1 `notin` fv_q_tm a1 ->
  m1 `notin` fv_q_tm a2 ->
  m1 `notin` fv_q_tm (subst_tm_tm a2 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_q_tm_subst_tm_tm_notin :
forall a1 a2 x1 m1,
  m1 `notin` fv_q_tm a1 ->
  m1 `notin` fv_q_tm a2 ->
  m1 `notin` fv_q_tm (subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve fv_q_tm_subst_tm_tm_notin : lngen.

(* begin hide *)

Lemma fv_q_tm_subst_q_tm_notin_mutual :
(forall a1 q1 m1 m2,
  m2 `notin` fv_q_tm a1 ->
  m2 `notin` fv_q_qexp q1 ->
  m2 `notin` fv_q_tm (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_q_tm_subst_q_tm_notin :
forall a1 q1 m1 m2,
  m2 `notin` fv_q_tm a1 ->
  m2 `notin` fv_q_qexp q1 ->
  m2 `notin` fv_q_tm (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve fv_q_tm_subst_q_tm_notin : lngen.

(* begin hide *)

Lemma fv_q_qexp_subst_q_qexp_upper_mutual :
(forall q1 q2 m1,
  fv_q_qexp (subst_q_qexp q2 m1 q1) [<=] fv_q_qexp q2 `union` remove m1 (fv_q_qexp q1)).
Proof. Admitted.

(* end hide *)

Lemma fv_q_qexp_subst_q_qexp_upper :
forall q1 q2 m1,
  fv_q_qexp (subst_q_qexp q2 m1 q1) [<=] fv_q_qexp q2 `union` remove m1 (fv_q_qexp q1).
Proof. Admitted.

Hint Resolve fv_q_qexp_subst_q_qexp_upper : lngen.

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

Hint Resolve fv_tm_tm_subst_tm_tm_upper : lngen.

(* begin hide *)

Lemma fv_tm_tm_subst_q_tm_upper_mutual :
(forall a1 q1 m1,
  fv_tm_tm (subst_q_tm q1 m1 a1) [<=] fv_tm_tm a1).
Proof. Admitted.

(* end hide *)

Lemma fv_tm_tm_subst_q_tm_upper :
forall a1 q1 m1,
  fv_tm_tm (subst_q_tm q1 m1 a1) [<=] fv_tm_tm a1.
Proof. Admitted.

Hint Resolve fv_tm_tm_subst_q_tm_upper : lngen.

(* begin hide *)

Lemma fv_q_tm_subst_tm_tm_upper_mutual :
(forall a1 a2 x1,
  fv_q_tm (subst_tm_tm a2 x1 a1) [<=] fv_q_tm a2 `union` fv_q_tm a1).
Proof. Admitted.

(* end hide *)

Lemma fv_q_tm_subst_tm_tm_upper :
forall a1 a2 x1,
  fv_q_tm (subst_tm_tm a2 x1 a1) [<=] fv_q_tm a2 `union` fv_q_tm a1.
Proof. Admitted.

Hint Resolve fv_q_tm_subst_tm_tm_upper : lngen.

(* begin hide *)

Lemma fv_q_tm_subst_q_tm_upper_mutual :
(forall a1 q1 m1,
  fv_q_tm (subst_q_tm q1 m1 a1) [<=] fv_q_qexp q1 `union` remove m1 (fv_q_tm a1)).
Proof. Admitted.

(* end hide *)

Lemma fv_q_tm_subst_q_tm_upper :
forall a1 q1 m1,
  fv_q_tm (subst_q_tm q1 m1 a1) [<=] fv_q_qexp q1 `union` remove m1 (fv_q_tm a1).
Proof. Admitted.

Hint Resolve fv_q_tm_subst_q_tm_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_q_qexp_close_qexp_wrt_qexp_rec_mutual :
(forall q2 q1 m1 m2 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  m1 <> m2 ->
  m2 `notin` fv_q_qexp q1 ->
  subst_q_qexp q1 m1 (close_qexp_wrt_qexp_rec n1 m2 q2) = close_qexp_wrt_qexp_rec n1 m2 (subst_q_qexp q1 m1 q2)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_qexp_close_qexp_wrt_qexp_rec :
forall q2 q1 m1 m2 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  m1 <> m2 ->
  m2 `notin` fv_q_qexp q1 ->
  subst_q_qexp q1 m1 (close_qexp_wrt_qexp_rec n1 m2 q2) = close_qexp_wrt_qexp_rec n1 m2 (subst_q_qexp q1 m1 q2).
Proof. Admitted.

Hint Resolve subst_q_qexp_close_qexp_wrt_qexp_rec : lngen.

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

Hint Resolve subst_tm_tm_close_tm_wrt_tm_rec : lngen.

(* begin hide *)

Lemma subst_tm_tm_close_tm_wrt_qexp_rec_mutual :
(forall a2 a1 m1 x1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  x1 `notin` fv_q_tm a1 ->
  subst_tm_tm a1 m1 (close_tm_wrt_qexp_rec n1 x1 a2) = close_tm_wrt_qexp_rec n1 x1 (subst_tm_tm a1 m1 a2)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_close_tm_wrt_qexp_rec :
forall a2 a1 m1 x1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  x1 `notin` fv_q_tm a1 ->
  subst_tm_tm a1 m1 (close_tm_wrt_qexp_rec n1 x1 a2) = close_tm_wrt_qexp_rec n1 x1 (subst_tm_tm a1 m1 a2).
Proof. Admitted.

Hint Resolve subst_tm_tm_close_tm_wrt_qexp_rec : lngen.

(* begin hide *)

Lemma subst_q_tm_close_tm_wrt_tm_rec_mutual :
(forall a1 q1 x1 m1 n1,
  subst_q_tm q1 x1 (close_tm_wrt_tm_rec n1 m1 a1) = close_tm_wrt_tm_rec n1 m1 (subst_q_tm q1 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_close_tm_wrt_tm_rec :
forall a1 q1 x1 m1 n1,
  subst_q_tm q1 x1 (close_tm_wrt_tm_rec n1 m1 a1) = close_tm_wrt_tm_rec n1 m1 (subst_q_tm q1 x1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_close_tm_wrt_tm_rec : lngen.

(* begin hide *)

Lemma subst_q_tm_close_tm_wrt_qexp_rec_mutual :
(forall a1 q1 m1 m2 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  m1 <> m2 ->
  m2 `notin` fv_q_qexp q1 ->
  subst_q_tm q1 m1 (close_tm_wrt_qexp_rec n1 m2 a1) = close_tm_wrt_qexp_rec n1 m2 (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_close_tm_wrt_qexp_rec :
forall a1 q1 m1 m2 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  m1 <> m2 ->
  m2 `notin` fv_q_qexp q1 ->
  subst_q_tm q1 m1 (close_tm_wrt_qexp_rec n1 m2 a1) = close_tm_wrt_qexp_rec n1 m2 (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_close_tm_wrt_qexp_rec : lngen.

Lemma subst_q_qexp_close_qexp_wrt_qexp :
forall q2 q1 m1 m2,
  lc_qexp q1 ->  m1 <> m2 ->
  m2 `notin` fv_q_qexp q1 ->
  subst_q_qexp q1 m1 (close_qexp_wrt_qexp m2 q2) = close_qexp_wrt_qexp m2 (subst_q_qexp q1 m1 q2).
Proof. Admitted.

Hint Resolve subst_q_qexp_close_qexp_wrt_qexp : lngen.

Lemma subst_tm_tm_close_tm_wrt_tm :
forall a2 a1 x1 x2,
  lc_tm a1 ->  x1 <> x2 ->
  x2 `notin` fv_tm_tm a1 ->
  subst_tm_tm a1 x1 (close_tm_wrt_tm x2 a2) = close_tm_wrt_tm x2 (subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve subst_tm_tm_close_tm_wrt_tm : lngen.

Lemma subst_tm_tm_close_tm_wrt_qexp :
forall a2 a1 m1 x1,
  lc_tm a1 ->  x1 `notin` fv_q_tm a1 ->
  subst_tm_tm a1 m1 (close_tm_wrt_qexp x1 a2) = close_tm_wrt_qexp x1 (subst_tm_tm a1 m1 a2).
Proof. Admitted.

Hint Resolve subst_tm_tm_close_tm_wrt_qexp : lngen.

Lemma subst_q_tm_close_tm_wrt_tm :
forall a1 q1 x1 m1,
  lc_qexp q1 ->  subst_q_tm q1 x1 (close_tm_wrt_tm m1 a1) = close_tm_wrt_tm m1 (subst_q_tm q1 x1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_close_tm_wrt_tm : lngen.

Lemma subst_q_tm_close_tm_wrt_qexp :
forall a1 q1 m1 m2,
  lc_qexp q1 ->  m1 <> m2 ->
  m2 `notin` fv_q_qexp q1 ->
  subst_q_tm q1 m1 (close_tm_wrt_qexp m2 a1) = close_tm_wrt_qexp m2 (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_close_tm_wrt_qexp : lngen.

(* begin hide *)

Lemma subst_q_qexp_degree_qexp_wrt_qexp_mutual :
(forall q1 q2 m1 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  degree_qexp_wrt_qexp n1 q2 ->
  degree_qexp_wrt_qexp n1 (subst_q_qexp q2 m1 q1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_qexp_degree_qexp_wrt_qexp :
forall q1 q2 m1 n1,
  degree_qexp_wrt_qexp n1 q1 ->
  degree_qexp_wrt_qexp n1 q2 ->
  degree_qexp_wrt_qexp n1 (subst_q_qexp q2 m1 q1).
Proof. Admitted.

Hint Resolve subst_q_qexp_degree_qexp_wrt_qexp : lngen.

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

Hint Resolve subst_tm_tm_degree_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_tm_tm_degree_tm_wrt_qexp_mutual :
(forall a1 a2 x1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp n1 a2 ->
  degree_tm_wrt_qexp n1 (subst_tm_tm a2 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_degree_tm_wrt_qexp :
forall a1 a2 x1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_tm_wrt_qexp n1 a2 ->
  degree_tm_wrt_qexp n1 (subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve subst_tm_tm_degree_tm_wrt_qexp : lngen.

(* begin hide *)

Lemma subst_q_tm_degree_tm_wrt_tm_mutual :
(forall a1 q1 m1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_degree_tm_wrt_tm :
forall a1 q1 m1 n1,
  degree_tm_wrt_tm n1 a1 ->
  degree_tm_wrt_tm n1 (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_degree_tm_wrt_tm : lngen.

(* begin hide *)

Lemma subst_q_tm_degree_tm_wrt_qexp_mutual :
(forall a1 q1 m1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_qexp_wrt_qexp n1 q1 ->
  degree_tm_wrt_qexp n1 (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_degree_tm_wrt_qexp :
forall a1 q1 m1 n1,
  degree_tm_wrt_qexp n1 a1 ->
  degree_qexp_wrt_qexp n1 q1 ->
  degree_tm_wrt_qexp n1 (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_degree_tm_wrt_qexp : lngen.

(* begin hide *)

Lemma subst_q_qexp_fresh_eq_mutual :
(forall q2 q1 m1,
  m1 `notin` fv_q_qexp q2 ->
  subst_q_qexp q1 m1 q2 = q2).
Proof. Admitted.

(* end hide *)

Lemma subst_q_qexp_fresh_eq :
forall q2 q1 m1,
  m1 `notin` fv_q_qexp q2 ->
  subst_q_qexp q1 m1 q2 = q2.
Proof. Admitted.

Hint Resolve subst_q_qexp_fresh_eq : lngen.
Hint Rewrite subst_q_qexp_fresh_eq using solve [auto] : lngen.

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

Hint Resolve subst_tm_tm_fresh_eq : lngen.
Hint Rewrite subst_tm_tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_q_tm_fresh_eq_mutual :
(forall a1 q1 m1,
  m1 `notin` fv_q_tm a1 ->
  subst_q_tm q1 m1 a1 = a1).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_fresh_eq :
forall a1 q1 m1,
  m1 `notin` fv_q_tm a1 ->
  subst_q_tm q1 m1 a1 = a1.
Proof. Admitted.

Hint Resolve subst_q_tm_fresh_eq : lngen.
Hint Rewrite subst_q_tm_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_q_qexp_fresh_same_mutual :
(forall q2 q1 m1,
  m1 `notin` fv_q_qexp q1 ->
  m1 `notin` fv_q_qexp (subst_q_qexp q1 m1 q2)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_qexp_fresh_same :
forall q2 q1 m1,
  m1 `notin` fv_q_qexp q1 ->
  m1 `notin` fv_q_qexp (subst_q_qexp q1 m1 q2).
Proof. Admitted.

Hint Resolve subst_q_qexp_fresh_same : lngen.

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

Hint Resolve subst_tm_tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_q_tm_fresh_same_mutual :
(forall a1 q1 m1,
  m1 `notin` fv_q_qexp q1 ->
  m1 `notin` fv_q_tm (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_fresh_same :
forall a1 q1 m1,
  m1 `notin` fv_q_qexp q1 ->
  m1 `notin` fv_q_tm (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_fresh_same : lngen.

(* begin hide *)

Lemma subst_q_qexp_fresh_mutual :
(forall q2 q1 m1 m2,
  m1 `notin` fv_q_qexp q2 ->
  m1 `notin` fv_q_qexp q1 ->
  m1 `notin` fv_q_qexp (subst_q_qexp q1 m2 q2)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_qexp_fresh :
forall q2 q1 m1 m2,
  m1 `notin` fv_q_qexp q2 ->
  m1 `notin` fv_q_qexp q1 ->
  m1 `notin` fv_q_qexp (subst_q_qexp q1 m2 q2).
Proof. Admitted.

Hint Resolve subst_q_qexp_fresh : lngen.

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

Hint Resolve subst_tm_tm_fresh : lngen.

(* begin hide *)

Lemma subst_q_tm_fresh_mutual :
(forall a1 q1 m1 m2,
  m1 `notin` fv_q_tm a1 ->
  m1 `notin` fv_q_qexp q1 ->
  m1 `notin` fv_q_tm (subst_q_tm q1 m2 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_fresh :
forall a1 q1 m1 m2,
  m1 `notin` fv_q_tm a1 ->
  m1 `notin` fv_q_qexp q1 ->
  m1 `notin` fv_q_tm (subst_q_tm q1 m2 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_fresh : lngen.

Lemma subst_q_qexp_lc_qexp :
forall q1 q2 m1,
  lc_qexp q1 ->
  lc_qexp q2 ->
  lc_qexp (subst_q_qexp q2 m1 q1).
Proof. Admitted.

Hint Resolve subst_q_qexp_lc_qexp : lngen.

Lemma subst_tm_tm_lc_tm :
forall a1 a2 x1,
  lc_tm a1 ->
  lc_tm a2 ->
  lc_tm (subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve subst_tm_tm_lc_tm : lngen.

Lemma subst_q_tm_lc_tm :
forall a1 q1 m1,
  lc_tm a1 ->
  lc_qexp q1 ->
  lc_tm (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_lc_tm : lngen.

(* begin hide *)

Lemma subst_q_qexp_open_qexp_wrt_qexp_rec_mutual :
(forall q3 q1 q2 m1 n1,
  lc_qexp q1 ->
  subst_q_qexp q1 m1 (open_qexp_wrt_qexp_rec n1 q2 q3) = open_qexp_wrt_qexp_rec n1 (subst_q_qexp q1 m1 q2) (subst_q_qexp q1 m1 q3)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_q_qexp_open_qexp_wrt_qexp_rec :
forall q3 q1 q2 m1 n1,
  lc_qexp q1 ->
  subst_q_qexp q1 m1 (open_qexp_wrt_qexp_rec n1 q2 q3) = open_qexp_wrt_qexp_rec n1 (subst_q_qexp q1 m1 q2) (subst_q_qexp q1 m1 q3).
Proof. Admitted.

Hint Resolve subst_q_qexp_open_qexp_wrt_qexp_rec : lngen.

(* end hide *)

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

Hint Resolve subst_tm_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_tm_open_tm_wrt_qexp_rec_mutual :
(forall a2 a1 q1 x1 n1,
  lc_tm a1 ->
  subst_tm_tm a1 x1 (open_tm_wrt_qexp_rec n1 q1 a2) = open_tm_wrt_qexp_rec n1 q1 (subst_tm_tm a1 x1 a2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_tm_tm_open_tm_wrt_qexp_rec :
forall a2 a1 q1 x1 n1,
  lc_tm a1 ->
  subst_tm_tm a1 x1 (open_tm_wrt_qexp_rec n1 q1 a2) = open_tm_wrt_qexp_rec n1 q1 (subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve subst_tm_tm_open_tm_wrt_qexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_open_tm_wrt_tm_rec_mutual :
(forall a2 q1 a1 m1 n1,
  subst_q_tm q1 m1 (open_tm_wrt_tm_rec n1 a1 a2) = open_tm_wrt_tm_rec n1 (subst_q_tm q1 m1 a1) (subst_q_tm q1 m1 a2)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_open_tm_wrt_tm_rec :
forall a2 q1 a1 m1 n1,
  subst_q_tm q1 m1 (open_tm_wrt_tm_rec n1 a1 a2) = open_tm_wrt_tm_rec n1 (subst_q_tm q1 m1 a1) (subst_q_tm q1 m1 a2).
Proof. Admitted.

Hint Resolve subst_q_tm_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_open_tm_wrt_qexp_rec_mutual :
(forall a1 q1 q2 m1 n1,
  lc_qexp q1 ->
  subst_q_tm q1 m1 (open_tm_wrt_qexp_rec n1 q2 a1) = open_tm_wrt_qexp_rec n1 (subst_q_qexp q1 m1 q2) (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_open_tm_wrt_qexp_rec :
forall a1 q1 q2 m1 n1,
  lc_qexp q1 ->
  subst_q_tm q1 m1 (open_tm_wrt_qexp_rec n1 q2 a1) = open_tm_wrt_qexp_rec n1 (subst_q_qexp q1 m1 q2) (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_open_tm_wrt_qexp_rec : lngen.

(* end hide *)

Lemma subst_q_qexp_open_qexp_wrt_qexp :
forall q3 q1 q2 m1,
  lc_qexp q1 ->
  subst_q_qexp q1 m1 (open_qexp_wrt_qexp q3 q2) = open_qexp_wrt_qexp (subst_q_qexp q1 m1 q3) (subst_q_qexp q1 m1 q2).
Proof. Admitted.

Hint Resolve subst_q_qexp_open_qexp_wrt_qexp : lngen.

Lemma subst_tm_tm_open_tm_wrt_tm :
forall a3 a1 a2 x1,
  lc_tm a1 ->
  subst_tm_tm a1 x1 (open_tm_wrt_tm a3 a2) = open_tm_wrt_tm (subst_tm_tm a1 x1 a3) (subst_tm_tm a1 x1 a2).
Proof. Admitted.

Hint Resolve subst_tm_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_tm_open_tm_wrt_qexp :
forall a2 a1 q1 x1,
  lc_tm a1 ->
  subst_tm_tm a1 x1 (open_tm_wrt_qexp a2 q1) = open_tm_wrt_qexp (subst_tm_tm a1 x1 a2) q1.
Proof. Admitted.

Hint Resolve subst_tm_tm_open_tm_wrt_qexp : lngen.

Lemma subst_q_tm_open_tm_wrt_tm :
forall a2 q1 a1 m1,
  subst_q_tm q1 m1 (open_tm_wrt_tm a2 a1) = open_tm_wrt_tm (subst_q_tm q1 m1 a2) (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_open_tm_wrt_tm : lngen.

Lemma subst_q_tm_open_tm_wrt_qexp :
forall a1 q1 q2 m1,
  lc_qexp q1 ->
  subst_q_tm q1 m1 (open_tm_wrt_qexp a1 q2) = open_tm_wrt_qexp (subst_q_tm q1 m1 a1) (subst_q_qexp q1 m1 q2).
Proof. Admitted.

Hint Resolve subst_q_tm_open_tm_wrt_qexp : lngen.

Lemma subst_q_qexp_open_qexp_wrt_qexp_var :
forall q2 q1 m1 m2,
  m1 <> m2 ->
  lc_qexp q1 ->
  open_qexp_wrt_qexp (subst_q_qexp q1 m1 q2) (q_Var_f m2) = subst_q_qexp q1 m1 (open_qexp_wrt_qexp q2 (q_Var_f m2)).
Proof. Admitted.

Hint Resolve subst_q_qexp_open_qexp_wrt_qexp_var : lngen.

Lemma subst_tm_tm_open_tm_wrt_tm_var :
forall a2 a1 x1 x2,
  x1 <> x2 ->
  lc_tm a1 ->
  open_tm_wrt_tm (subst_tm_tm a1 x1 a2) (a_Var_f x2) = subst_tm_tm a1 x1 (open_tm_wrt_tm a2 (a_Var_f x2)).
Proof. Admitted.

Hint Resolve subst_tm_tm_open_tm_wrt_tm_var : lngen.

Lemma subst_tm_tm_open_tm_wrt_qexp_var :
forall a2 a1 x1 m1,
  lc_tm a1 ->
  open_tm_wrt_qexp (subst_tm_tm a1 x1 a2) (q_Var_f m1) = subst_tm_tm a1 x1 (open_tm_wrt_qexp a2 (q_Var_f m1)).
Proof. Admitted.

Hint Resolve subst_tm_tm_open_tm_wrt_qexp_var : lngen.

Lemma subst_q_tm_open_tm_wrt_tm_var :
forall a1 q1 m1 x1,
  open_tm_wrt_tm (subst_q_tm q1 m1 a1) (a_Var_f x1) = subst_q_tm q1 m1 (open_tm_wrt_tm a1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve subst_q_tm_open_tm_wrt_tm_var : lngen.

Lemma subst_q_tm_open_tm_wrt_qexp_var :
forall a1 q1 m1 m2,
  m1 <> m2 ->
  lc_qexp q1 ->
  open_tm_wrt_qexp (subst_q_tm q1 m1 a1) (q_Var_f m2) = subst_q_tm q1 m1 (open_tm_wrt_qexp a1 (q_Var_f m2)).
Proof. Admitted.

Hint Resolve subst_q_tm_open_tm_wrt_qexp_var : lngen.

(* begin hide *)

Lemma subst_q_qexp_spec_rec_mutual :
(forall q1 q2 m1 n1,
  subst_q_qexp q2 m1 q1 = open_qexp_wrt_qexp_rec n1 q2 (close_qexp_wrt_qexp_rec n1 m1 q1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_q_qexp_spec_rec :
forall q1 q2 m1 n1,
  subst_q_qexp q2 m1 q1 = open_qexp_wrt_qexp_rec n1 q2 (close_qexp_wrt_qexp_rec n1 m1 q1).
Proof. Admitted.

Hint Resolve subst_q_qexp_spec_rec : lngen.

(* end hide *)

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

Hint Resolve subst_tm_tm_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_spec_rec_mutual :
(forall a1 q1 m1 n1,
  subst_q_tm q1 m1 a1 = open_tm_wrt_qexp_rec n1 q1 (close_tm_wrt_qexp_rec n1 m1 a1)).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_spec_rec :
forall a1 q1 m1 n1,
  subst_q_tm q1 m1 a1 = open_tm_wrt_qexp_rec n1 q1 (close_tm_wrt_qexp_rec n1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_spec_rec : lngen.

(* end hide *)

Lemma subst_q_qexp_spec :
forall q1 q2 m1,
  subst_q_qexp q2 m1 q1 = open_qexp_wrt_qexp (close_qexp_wrt_qexp m1 q1) q2.
Proof. Admitted.

Hint Resolve subst_q_qexp_spec : lngen.

Lemma subst_tm_tm_spec :
forall a1 a2 x1,
  subst_tm_tm a2 x1 a1 = open_tm_wrt_tm (close_tm_wrt_tm x1 a1) a2.
Proof. Admitted.

Hint Resolve subst_tm_tm_spec : lngen.

Lemma subst_q_tm_spec :
forall a1 q1 m1,
  subst_q_tm q1 m1 a1 = open_tm_wrt_qexp (close_tm_wrt_qexp m1 a1) q1.
Proof. Admitted.

Hint Resolve subst_q_tm_spec : lngen.

(* begin hide *)

Lemma subst_q_qexp_subst_q_qexp_mutual :
(forall q1 q2 q3 m2 m1,
  m2 `notin` fv_q_qexp q2 ->
  m2 <> m1 ->
  subst_q_qexp q2 m1 (subst_q_qexp q3 m2 q1) = subst_q_qexp (subst_q_qexp q2 m1 q3) m2 (subst_q_qexp q2 m1 q1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_qexp_subst_q_qexp :
forall q1 q2 q3 m2 m1,
  m2 `notin` fv_q_qexp q2 ->
  m2 <> m1 ->
  subst_q_qexp q2 m1 (subst_q_qexp q3 m2 q1) = subst_q_qexp (subst_q_qexp q2 m1 q3) m2 (subst_q_qexp q2 m1 q1).
Proof. Admitted.

Hint Resolve subst_q_qexp_subst_q_qexp : lngen.

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

Hint Resolve subst_tm_tm_subst_tm_tm : lngen.

(* begin hide *)

Lemma subst_tm_tm_subst_q_tm_mutual :
(forall a1 a2 q1 m1 x1,
  m1 `notin` fv_q_tm a2 ->
  subst_tm_tm a2 x1 (subst_q_tm q1 m1 a1) = subst_q_tm q1 m1 (subst_tm_tm a2 x1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_tm_tm_subst_q_tm :
forall a1 a2 q1 m1 x1,
  m1 `notin` fv_q_tm a2 ->
  subst_tm_tm a2 x1 (subst_q_tm q1 m1 a1) = subst_q_tm q1 m1 (subst_tm_tm a2 x1 a1).
Proof. Admitted.

Hint Resolve subst_tm_tm_subst_q_tm : lngen.

(* begin hide *)

Lemma subst_q_tm_subst_tm_tm_mutual :
(forall a1 q1 a2 x1 m1,
  subst_q_tm q1 m1 (subst_tm_tm a2 x1 a1) = subst_tm_tm (subst_q_tm q1 m1 a2) x1 (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_subst_tm_tm :
forall a1 q1 a2 x1 m1,
  subst_q_tm q1 m1 (subst_tm_tm a2 x1 a1) = subst_tm_tm (subst_q_tm q1 m1 a2) x1 (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_subst_tm_tm : lngen.

(* begin hide *)

Lemma subst_q_tm_subst_q_tm_mutual :
(forall a1 q1 q2 m2 m1,
  m2 `notin` fv_q_qexp q1 ->
  m2 <> m1 ->
  subst_q_tm q1 m1 (subst_q_tm q2 m2 a1) = subst_q_tm (subst_q_qexp q1 m1 q2) m2 (subst_q_tm q1 m1 a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_subst_q_tm :
forall a1 q1 q2 m2 m1,
  m2 `notin` fv_q_qexp q1 ->
  m2 <> m1 ->
  subst_q_tm q1 m1 (subst_q_tm q2 m2 a1) = subst_q_tm (subst_q_qexp q1 m1 q2) m2 (subst_q_tm q1 m1 a1).
Proof. Admitted.

Hint Resolve subst_q_tm_subst_q_tm : lngen.

(* begin hide *)

Lemma subst_q_qexp_close_qexp_wrt_qexp_rec_open_qexp_wrt_qexp_rec_mutual :
(forall q2 q1 m1 m2 n1,
  m2 `notin` fv_q_qexp q2 ->
  m2 `notin` fv_q_qexp q1 ->
  m2 <> m1 ->
  degree_qexp_wrt_qexp n1 q1 ->
  subst_q_qexp q1 m1 q2 = close_qexp_wrt_qexp_rec n1 m2 (subst_q_qexp q1 m1 (open_qexp_wrt_qexp_rec n1 (q_Var_f m2) q2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_q_qexp_close_qexp_wrt_qexp_rec_open_qexp_wrt_qexp_rec :
forall q2 q1 m1 m2 n1,
  m2 `notin` fv_q_qexp q2 ->
  m2 `notin` fv_q_qexp q1 ->
  m2 <> m1 ->
  degree_qexp_wrt_qexp n1 q1 ->
  subst_q_qexp q1 m1 q2 = close_qexp_wrt_qexp_rec n1 m2 (subst_q_qexp q1 m1 (open_qexp_wrt_qexp_rec n1 (q_Var_f m2) q2)).
Proof. Admitted.

Hint Resolve subst_q_qexp_close_qexp_wrt_qexp_rec_open_qexp_wrt_qexp_rec : lngen.

(* end hide *)

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

Hint Resolve subst_tm_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tm_tm_close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec_mutual :
(forall a2 a1 x1 m1 n1,
  m1 `notin` fv_q_tm a2 ->
  m1 `notin` fv_q_tm a1 ->
  degree_tm_wrt_qexp n1 a1 ->
  subst_tm_tm a1 x1 a2 = close_tm_wrt_qexp_rec n1 m1 (subst_tm_tm a1 x1 (open_tm_wrt_qexp_rec n1 (q_Var_f m1) a2))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_tm_tm_close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec :
forall a2 a1 x1 m1 n1,
  m1 `notin` fv_q_tm a2 ->
  m1 `notin` fv_q_tm a1 ->
  degree_tm_wrt_qexp n1 a1 ->
  subst_tm_tm a1 x1 a2 = close_tm_wrt_qexp_rec n1 m1 (subst_tm_tm a1 x1 (open_tm_wrt_qexp_rec n1 (q_Var_f m1) a2)).
Proof. Admitted.

Hint Resolve subst_tm_tm_close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec_mutual :
(forall a1 q1 m1 x1 n1,
  x1 `notin` fv_tm_tm a1 ->
  subst_q_tm q1 m1 a1 = close_tm_wrt_tm_rec n1 x1 (subst_q_tm q1 m1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec :
forall a1 q1 m1 x1 n1,
  x1 `notin` fv_tm_tm a1 ->
  subst_q_tm q1 m1 a1 = close_tm_wrt_tm_rec n1 x1 (subst_q_tm q1 m1 (open_tm_wrt_tm_rec n1 (a_Var_f x1) a1)).
Proof. Admitted.

Hint Resolve subst_q_tm_close_tm_wrt_tm_rec_open_tm_wrt_tm_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec_mutual :
(forall a1 q1 m1 m2 n1,
  m2 `notin` fv_q_tm a1 ->
  m2 `notin` fv_q_qexp q1 ->
  m2 <> m1 ->
  degree_qexp_wrt_qexp n1 q1 ->
  subst_q_tm q1 m1 a1 = close_tm_wrt_qexp_rec n1 m2 (subst_q_tm q1 m1 (open_tm_wrt_qexp_rec n1 (q_Var_f m2) a1))).
Proof. Admitted.

(* end hide *)

(* begin hide *)

Lemma subst_q_tm_close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec :
forall a1 q1 m1 m2 n1,
  m2 `notin` fv_q_tm a1 ->
  m2 `notin` fv_q_qexp q1 ->
  m2 <> m1 ->
  degree_qexp_wrt_qexp n1 q1 ->
  subst_q_tm q1 m1 a1 = close_tm_wrt_qexp_rec n1 m2 (subst_q_tm q1 m1 (open_tm_wrt_qexp_rec n1 (q_Var_f m2) a1)).
Proof. Admitted.

Hint Resolve subst_q_tm_close_tm_wrt_qexp_rec_open_tm_wrt_qexp_rec : lngen.

(* end hide *)

Lemma subst_q_qexp_close_qexp_wrt_qexp_open_qexp_wrt_qexp :
forall q2 q1 m1 m2,
  m2 `notin` fv_q_qexp q2 ->
  m2 `notin` fv_q_qexp q1 ->
  m2 <> m1 ->
  lc_qexp q1 ->
  subst_q_qexp q1 m1 q2 = close_qexp_wrt_qexp m2 (subst_q_qexp q1 m1 (open_qexp_wrt_qexp q2 (q_Var_f m2))).
Proof. Admitted.

Hint Resolve subst_q_qexp_close_qexp_wrt_qexp_open_qexp_wrt_qexp : lngen.

Lemma subst_tm_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall a2 a1 x1 x2,
  x2 `notin` fv_tm_tm a2 ->
  x2 `notin` fv_tm_tm a1 ->
  x2 <> x1 ->
  lc_tm a1 ->
  subst_tm_tm a1 x1 a2 = close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm a2 (a_Var_f x2))).
Proof. Admitted.

Hint Resolve subst_tm_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma subst_tm_tm_close_tm_wrt_qexp_open_tm_wrt_qexp :
forall a2 a1 x1 m1,
  m1 `notin` fv_q_tm a2 ->
  m1 `notin` fv_q_tm a1 ->
  lc_tm a1 ->
  subst_tm_tm a1 x1 a2 = close_tm_wrt_qexp m1 (subst_tm_tm a1 x1 (open_tm_wrt_qexp a2 (q_Var_f m1))).
Proof. Admitted.

Hint Resolve subst_tm_tm_close_tm_wrt_qexp_open_tm_wrt_qexp : lngen.

Lemma subst_q_tm_close_tm_wrt_tm_open_tm_wrt_tm :
forall a1 q1 m1 x1,
  x1 `notin` fv_tm_tm a1 ->
  lc_qexp q1 ->
  subst_q_tm q1 m1 a1 = close_tm_wrt_tm x1 (subst_q_tm q1 m1 (open_tm_wrt_tm a1 (a_Var_f x1))).
Proof. Admitted.

Hint Resolve subst_q_tm_close_tm_wrt_tm_open_tm_wrt_tm : lngen.

Lemma subst_q_tm_close_tm_wrt_qexp_open_tm_wrt_qexp :
forall a1 q1 m1 m2,
  m2 `notin` fv_q_tm a1 ->
  m2 `notin` fv_q_qexp q1 ->
  m2 <> m1 ->
  lc_qexp q1 ->
  subst_q_tm q1 m1 a1 = close_tm_wrt_qexp m2 (subst_q_tm q1 m1 (open_tm_wrt_qexp a1 (q_Var_f m2))).
Proof. Admitted.

Hint Resolve subst_q_tm_close_tm_wrt_qexp_open_tm_wrt_qexp : lngen.

Lemma subst_tm_tm_a_Pi :
forall x2 q1 A1 B1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm B1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_Pi q1 A1 B1) = a_Pi (q1) (subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm B1 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve subst_tm_tm_a_Pi : lngen.

Lemma subst_tm_tm_a_Lam :
forall x2 q1 A1 a2 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm a2 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_Lam q1 A1 a2) = a_Lam (q1) (subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm a2 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve subst_tm_tm_a_Lam : lngen.

Lemma subst_tm_tm_a_LetBoxB :
forall x2 a2 b1 B1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm b1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_LetBoxB a2 b1 B1) = a_LetBoxB (subst_tm_tm a1 x1 a2) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm b1 (a_Var_f x2)))) (subst_tm_tm a1 x1 B1).
Proof. Admitted.

Hint Resolve subst_tm_tm_a_LetBoxB : lngen.

Lemma subst_tm_tm_a_Let :
forall x2 a2 b1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm b1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_Let a2 b1) = a_Let (subst_tm_tm a1 x1 a2) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm b1 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve subst_tm_tm_a_Let : lngen.

Lemma subst_tm_tm_a_Sigma :
forall x2 q1 A1 B1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm B1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_Sigma q1 A1 B1) = a_Sigma (q1) (subst_tm_tm a1 x1 A1) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm B1 (a_Var_f x2)))).
Proof. Admitted.

Hint Resolve subst_tm_tm_a_Sigma : lngen.

Lemma subst_tm_tm_a_Spread :
forall x2 a2 b1 B1 a1 x1,
  lc_tm a1 ->
  x2 `notin` fv_tm_tm a1 `union` fv_tm_tm b1 `union` singleton x1 ->
  subst_tm_tm a1 x1 (a_Spread a2 b1 B1) = a_Spread (subst_tm_tm a1 x1 a2) (close_tm_wrt_tm x2 (subst_tm_tm a1 x1 (open_tm_wrt_tm b1 (a_Var_f x2)))) (subst_tm_tm a1 x1 B1).
Proof. Admitted.

Hint Resolve subst_tm_tm_a_Spread : lngen.

Lemma subst_tm_tm_a_AllU :
forall m1 A1 a1 x1,
  lc_tm a1 ->
  m1 `notin` fv_q_tm a1 `union` fv_q_tm A1 ->
  subst_tm_tm a1 x1 (a_AllU A1) = a_AllU (close_tm_wrt_qexp m1 (subst_tm_tm a1 x1 (open_tm_wrt_qexp A1 (q_Var_f m1)))).
Proof. Admitted.

Hint Resolve subst_tm_tm_a_AllU : lngen.

Lemma subst_tm_tm_a_LamU :
forall m1 a2 a1 x1,
  lc_tm a1 ->
  m1 `notin` fv_q_tm a1 `union` fv_q_tm a2 ->
  subst_tm_tm a1 x1 (a_LamU a2) = a_LamU (close_tm_wrt_qexp m1 (subst_tm_tm a1 x1 (open_tm_wrt_qexp a2 (q_Var_f m1)))).
Proof. Admitted.

Hint Resolve subst_tm_tm_a_LamU : lngen.

Lemma subst_q_tm_a_Pi :
forall x1 q2 A1 B1 q1 m1,
  lc_qexp q1 ->
  x1 `notin` fv_tm_tm B1 ->
  subst_q_tm q1 m1 (a_Pi q2 A1 B1) = a_Pi (subst_q_qexp q1 m1 q2) (subst_q_tm q1 m1 A1) (close_tm_wrt_tm x1 (subst_q_tm q1 m1 (open_tm_wrt_tm B1 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve subst_q_tm_a_Pi : lngen.

Lemma subst_q_tm_a_Lam :
forall x1 q2 A1 a1 q1 m1,
  lc_qexp q1 ->
  x1 `notin` fv_tm_tm a1 ->
  subst_q_tm q1 m1 (a_Lam q2 A1 a1) = a_Lam (subst_q_qexp q1 m1 q2) (subst_q_tm q1 m1 A1) (close_tm_wrt_tm x1 (subst_q_tm q1 m1 (open_tm_wrt_tm a1 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve subst_q_tm_a_Lam : lngen.

Lemma subst_q_tm_a_LetBoxB :
forall x1 a1 b1 B1 q1 m1,
  lc_qexp q1 ->
  x1 `notin` fv_tm_tm b1 ->
  subst_q_tm q1 m1 (a_LetBoxB a1 b1 B1) = a_LetBoxB (subst_q_tm q1 m1 a1) (close_tm_wrt_tm x1 (subst_q_tm q1 m1 (open_tm_wrt_tm b1 (a_Var_f x1)))) (subst_q_tm q1 m1 B1).
Proof. Admitted.

Hint Resolve subst_q_tm_a_LetBoxB : lngen.

Lemma subst_q_tm_a_Let :
forall x1 a1 b1 q1 m1,
  lc_qexp q1 ->
  x1 `notin` fv_tm_tm b1 ->
  subst_q_tm q1 m1 (a_Let a1 b1) = a_Let (subst_q_tm q1 m1 a1) (close_tm_wrt_tm x1 (subst_q_tm q1 m1 (open_tm_wrt_tm b1 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve subst_q_tm_a_Let : lngen.

Lemma subst_q_tm_a_Sigma :
forall x1 q2 A1 B1 q1 m1,
  lc_qexp q1 ->
  x1 `notin` fv_tm_tm B1 ->
  subst_q_tm q1 m1 (a_Sigma q2 A1 B1) = a_Sigma (subst_q_qexp q1 m1 q2) (subst_q_tm q1 m1 A1) (close_tm_wrt_tm x1 (subst_q_tm q1 m1 (open_tm_wrt_tm B1 (a_Var_f x1)))).
Proof. Admitted.

Hint Resolve subst_q_tm_a_Sigma : lngen.

Lemma subst_q_tm_a_Spread :
forall x1 a1 b1 B1 q1 m1,
  lc_qexp q1 ->
  x1 `notin` fv_tm_tm b1 ->
  subst_q_tm q1 m1 (a_Spread a1 b1 B1) = a_Spread (subst_q_tm q1 m1 a1) (close_tm_wrt_tm x1 (subst_q_tm q1 m1 (open_tm_wrt_tm b1 (a_Var_f x1)))) (subst_q_tm q1 m1 B1).
Proof. Admitted.

Hint Resolve subst_q_tm_a_Spread : lngen.

Lemma subst_q_tm_a_AllU :
forall m2 A1 q1 m1,
  lc_qexp q1 ->
  m2 `notin` fv_q_qexp q1 `union` fv_q_tm A1 `union` singleton m1 ->
  subst_q_tm q1 m1 (a_AllU A1) = a_AllU (close_tm_wrt_qexp m2 (subst_q_tm q1 m1 (open_tm_wrt_qexp A1 (q_Var_f m2)))).
Proof. Admitted.

Hint Resolve subst_q_tm_a_AllU : lngen.

Lemma subst_q_tm_a_LamU :
forall m2 a1 q1 m1,
  lc_qexp q1 ->
  m2 `notin` fv_q_qexp q1 `union` fv_q_tm a1 `union` singleton m1 ->
  subst_q_tm q1 m1 (a_LamU a1) = a_LamU (close_tm_wrt_qexp m2 (subst_q_tm q1 m1 (open_tm_wrt_qexp a1 (q_Var_f m2)))).
Proof. Admitted.

Hint Resolve subst_q_tm_a_LamU : lngen.

(* begin hide *)

Lemma subst_q_qexp_intro_rec_mutual :
(forall q1 m1 q2 n1,
  m1 `notin` fv_q_qexp q1 ->
  open_qexp_wrt_qexp_rec n1 q2 q1 = subst_q_qexp q2 m1 (open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_qexp_intro_rec :
forall q1 m1 q2 n1,
  m1 `notin` fv_q_qexp q1 ->
  open_qexp_wrt_qexp_rec n1 q2 q1 = subst_q_qexp q2 m1 (open_qexp_wrt_qexp_rec n1 (q_Var_f m1) q1).
Proof. Admitted.

Hint Resolve subst_q_qexp_intro_rec : lngen.
Hint Rewrite subst_q_qexp_intro_rec using solve [auto] : lngen.

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

Hint Resolve subst_tm_tm_intro_rec : lngen.
Hint Rewrite subst_tm_tm_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_q_tm_intro_rec_mutual :
(forall a1 m1 q1 n1,
  m1 `notin` fv_q_tm a1 ->
  open_tm_wrt_qexp_rec n1 q1 a1 = subst_q_tm q1 m1 (open_tm_wrt_qexp_rec n1 (q_Var_f m1) a1)).
Proof. Admitted.

(* end hide *)

Lemma subst_q_tm_intro_rec :
forall a1 m1 q1 n1,
  m1 `notin` fv_q_tm a1 ->
  open_tm_wrt_qexp_rec n1 q1 a1 = subst_q_tm q1 m1 (open_tm_wrt_qexp_rec n1 (q_Var_f m1) a1).
Proof. Admitted.

Hint Resolve subst_q_tm_intro_rec : lngen.
Hint Rewrite subst_q_tm_intro_rec using solve [auto] : lngen.

Lemma subst_q_qexp_intro :
forall m1 q1 q2,
  m1 `notin` fv_q_qexp q1 ->
  open_qexp_wrt_qexp q1 q2 = subst_q_qexp q2 m1 (open_qexp_wrt_qexp q1 (q_Var_f m1)).
Proof. Admitted.

Hint Resolve subst_q_qexp_intro : lngen.

Lemma subst_tm_tm_intro :
forall x1 a1 a2,
  x1 `notin` fv_tm_tm a1 ->
  open_tm_wrt_tm a1 a2 = subst_tm_tm a2 x1 (open_tm_wrt_tm a1 (a_Var_f x1)).
Proof. Admitted.

Hint Resolve subst_tm_tm_intro : lngen.

Lemma subst_q_tm_intro :
forall m1 a1 q1,
  m1 `notin` fv_q_tm a1 ->
  open_tm_wrt_qexp a1 q1 = subst_q_tm q1 m1 (open_tm_wrt_qexp a1 (q_Var_f m1)).
Proof. Admitted.

Hint Resolve subst_q_tm_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
