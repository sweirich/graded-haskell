Require Import ssreflect.
Require Import Metalib.Metatheory.
Require Import dqtt_ott.

(* only for locally-closed terms *)
Axiom Beta_lc1 : forall A B, Beta A B -> lc_tm A.
Axiom Beta_lc2 : forall A B, Beta A B -> lc_tm B.


Axiom B_Refl : forall (A:tm),
     lc_tm A ->
     Beta A A.

Axiom B_Sym : forall (A B:tm),
     Beta B A ->
     Beta A B.
Axiom B_Trans : forall (A B A1:tm),
     Beta A A1 ->
     Beta A1 B ->
     Beta A B.
Axiom B_Step : forall (a a':tm),
     Step a a' ->
     Beta a a'.

Hint Resolve B_Refl B_Sym B_Trans B_Step : core.

Axiom subst_Beta1 : forall a0 x A B, lc_tm a0 -> Beta A B -> Beta (subst_tm_tm a0 x A) (subst_tm_tm a0 x B).
Axiom subst_Beta2 : forall a0 a1 x B, lc_tm B -> Beta a0 a1 -> Beta (subst_tm_tm a0 x B) (subst_tm_tm a1 x B).
Axiom subst_Beta : forall a0 a1 x A B, Beta a0 a1 -> Beta A B -> Beta (subst_tm_tm a0 x A) (subst_tm_tm a1 x B).

Axiom invert_Beta_a_Pi0 : forall {q A B q0 A0 B0 }, Beta (a_Pi q A B) (a_Pi q0 A0 B0) -> q = q0.
Axiom invert_Beta_a_Pi1 : forall {q A B q0 A0 B0 }, Beta (a_Pi q A B) (a_Pi q0 A0 B0) -> Beta A A0.
Axiom invert_Beta_a_Pi2 : forall {q A B q0 A0 B0 }, Beta (a_Pi q A B) (a_Pi q0 A0 B0) -> 
       forall x, x `notin` fv_tm_tm B \u fv_tm_tm B0 ->                                             
                 Beta (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B0 (a_Var_f x)).

Axiom invert_Beta_a_Sigma0 : forall {q A B q0 A0 B0 }, Beta (a_Sigma q A B) (a_Sigma q0 A0 B0) -> q = q0.
Axiom invert_Beta_a_Sigma1 : forall {q A B q0 A0 B0 }, Beta (a_Sigma q A B) (a_Sigma q0 A0 B0) -> Beta A A0.
Axiom invert_Beta_a_Sigma2 : forall {q A B q0 A0 B0 }, Beta (a_Sigma q A B) (a_Sigma q0 A0 B0) -> 
       forall x, x `notin` fv_tm_tm B \u fv_tm_tm B0 ->                                             
                 Beta (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B0 (a_Var_f x)).


Axiom invert_Beta_Box1 : forall {q1 q2 A B},  Beta (a_Box q1 A) (a_Box q2 B) -> Beta A B.
Axiom invert_Beta_Box2 : forall {q1 q2 A B},  Beta (a_Box q1 A) (a_Box q2 B) -> q1 = q2.

Axiom invert_Beta_Sum1 : forall {A1 B1 A2 B2},  Beta (a_Sum A1 B1) (a_Sum A2 B2) -> Beta A1 A2.
Axiom invert_Beta_Sum2 : forall {A1 B1 A2 B2},  Beta (a_Sum A1 B1) (a_Sum A2 B2) -> Beta B1 B2.


Inductive consistent : tm -> tm -> Prop :=
  | con_Type : consistent a_Type a_Type
  | con_Unit : consistent a_TyUnit a_TyUnit
  | con_Pi   : forall q A B q' A' B', consistent (a_Pi q A B) (a_Pi q' A' B')
  | con_Sigma : forall q A B q' A' B', consistent (a_Sigma q A B) (a_Sigma q' A' B')
  | con_Box  : forall q A A', consistent (a_Box q A) (a_Box q A')
  | con_Sum  : forall A B A' B', consistent (a_Sum A B) (a_Sum A' B')
  | con_unit : consistent a_TmUnit a_TmUnit
  | con_lam  : forall q A a A' a', consistent (a_Lam q A a) (a_Lam q A' a')
  | con_box  : forall q q' a a', consistent (a_box q a) (a_box q' a')
  | con_inj1 : forall a a', consistent (a_Inj1 a) (a_Inj1 a')
  | con_inj2 : forall a a', consistent (a_Inj2 a) (a_Inj2 a')
.
Hint Constructors consistent : core.

Inductive ty : tm -> Prop :=
| ty_Type : ty a_Type
| ty_Unit : ty a_TyUnit
| ty_Pi   : forall q A B, ty (a_Pi q A B)
| ty_Sigma : forall q A B, ty (a_Sigma q A B)
| ty_Box  : forall q A, ty (a_Box q A)
| ty_Sum  : forall A B, ty (a_Sum A B)
.

Inductive value : tm -> Prop :=
  | val_ty     : forall t, ty t -> value t
  | val_unit   : value a_TmUnit
  | val_lam    : forall q A a, value (a_Lam q A a)
  | val_box    : forall q a, value (a_box q a)
  | val_inj1   : forall a, value (a_Inj1 a)
  | val_inj2   : forall a, value (a_Inj2 a)
  | val_tensor : forall a b, value (a_Tensor a b)
.
Hint Constructors ty value : core.

Axiom Beta_consistent : forall A B, Beta A B -> value A -> value B -> consistent A B.
