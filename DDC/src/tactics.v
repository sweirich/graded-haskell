Require Export Qual.Qualitative_ott.
Require Export Qual.Qualitative_inf.
Require Export Metalib.LibTactics.
Require Export ssreflect.
Require Export Coq.Program.Equality.

Set Implicit Arguments.
Open Scope grade_scope.

Scheme GEq_ind' := Induction for GEq Sort Prop
   with CEq_ind'   := Induction for CEq Sort Prop.

Combined Scheme CEq_GEq_mutual
  from CEq_ind', GEq_ind'.


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : context => dom x) in
  let D := gather_atoms_with (fun x => fv_tm_tm x) in
  let E := gather_atoms_with (fun x : econtext => dom x) in
  constr:(A \u B \u C \u D \u E).

(* -------------------------------------------- *)

Ltac split_hyp :=
  repeat (
      match goal with
        | [ H : _ /\ _ |- _ ] => destruct H
      end).

Ltac invert_equality := 
  repeat match goal with 
    | [H : (_,_) = (_,_) |- _ ] => inversion H; subst; clear H
    | [H : (_,_,_) = (_,_,_) |- _ ] => inversion H; subst; clear H
    | [H : (_,_,_,_) = (_,_,_,_) |- _ ] => inversion H; subst; clear H
    | [H : [_] ++ _ = [_] ++ _ |- _ ] => inversion H; subst; clear H
    | [H : ( _ :: _ ) = ( _ :: _ )  |- _ ] => inversion H; subst; clear H
  end.

Ltac spec y := 
  let h0 := fresh in 
  match goal with [H0 : forall x : atom, x \notin ?L -> _ |- _ ] => 
     move: (H0 y ltac:(auto)) => h0; clear H0 end.

(* -------------------------------------------- *)

(* Local closure: we know that Ott produced relations are always locally closed. So it does not 
   hurt to axiomatize this fact. *)

(*
Lemma CEq_GEq_lc : 
  (forall P phi phi0 a b,
  CEq P phi phi0 a b -> lc_tm a /\ lc_tm b) /\
  (forall P phi a b,
  GEq P phi a b -> lc_tm a /\ lc_tm b).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; split_hyp; split; eauto.
*)


Axiom Step_lc1 : forall {a b}, Step a b -> lc_tm a.
Axiom Step_lc2 : forall {a b}, Step a b -> lc_tm b.

Axiom Grade_lc : forall {P psi a}, Grade P psi a -> lc_tm a.
Axiom GEq_lc1 : forall {W a psi b}, GEq W psi a b -> lc_tm a.
Axiom GEq_lc2 : forall {W a psi b}, GEq W psi a b -> lc_tm b.
Axiom DefEq_lc1 : forall {W a psi b}, DefEq W psi a b -> lc_tm a.
Axiom DefEq_lc2 : forall {W a psi b}, DefEq W psi a b -> lc_tm b.
Axiom Par_lc1 : forall {G a psi a'}, Par G psi a a' -> lc_tm a.
Axiom Par_lc2 : forall {G a psi a'}, Par G psi a a' -> lc_tm a'.
Axiom Typing_lc1 : forall {G psi a A}, Typing G psi a A -> lc_tm a.
Axiom Typing_lc2 : forall {G psi a A}, Typing G psi a A -> lc_tm A.

Axiom MultiPar_lc1 : forall {G a psi a'}, MultiPar G psi a a' -> lc_tm a.
Axiom MultiPar_lc2 : forall {G a psi a'}, MultiPar G psi a a' -> lc_tm a'.
Axiom ValueType_lc : forall {A}, ValueType A -> lc_tm A.
Axiom Consistent_lc1 : forall {a b}, Consistent a b -> lc_tm a.
Axiom Consistent_lc2 : forall {a b}, Consistent a b -> lc_tm b.
Axiom Joins_lc1 : forall {G a psi a'}, Joins G psi a a' -> lc_tm a.
Axiom Joins_lc2 : forall {G a psi a'}, Joins G psi a a' -> lc_tm a'.


Axiom CGrade_lc : forall {P psi phi a}, CGrade P psi phi a -> lc_tm a.
Axiom CEq_lc1 : forall {W a psi phi b}, CEq W psi phi a b -> lc_tm a.
Axiom CEq_lc2 : forall {W a psi phi b}, CEq W psi phi a b -> lc_tm b.
Axiom CDefEq_lc1 : forall {W a psi phi b}, CDefEq W psi phi a b -> lc_tm a. 
Axiom CDefEq_lc2 : forall {W a psi phi b}, CDefEq W psi phi a b -> lc_tm b. 
Axiom CPar_lc1 : forall {G a psi phi a'}, CPar G psi phi a a' -> lc_tm a.
Axiom CPar_lc2 : forall {G a psi phi a'}, CPar G psi phi a a' -> lc_tm a'.
Axiom CMultiPar_lc1 : forall {G a psi psi0 a'}, CMultiPar G psi psi0 a a' -> lc_tm a.
Axiom CMultiPar_lc2 : forall {G a psi psi0 a'}, CMultiPar G psi psi0 a a' -> lc_tm a'.
Axiom CTyping_lc1 : forall W q a A, CTyping W q a A -> lc_tm a. 
Axiom CTyping_lc2 : forall W q a A, CTyping W q a A -> lc_tm A. 
Axiom CJoins_lc1 : forall {G a psi phi a'}, CJoins G psi phi a a' -> lc_tm a.
Axiom CJoins_lc2 : forall {G a psi phi a'}, CJoins G psi phi a a' -> lc_tm a'.



(* Rewriting rules for subst *)

Lemma subst_tm_tm_var : forall a x, subst_tm_tm a x (a_Var_f x) = a.
Proof. intros. simpl. destruct (x == x). auto. done. Qed.
Lemma subst_tm_tm_var_neq : forall a x y, y <> x -> subst_tm_tm a x (a_Var_f y) = a_Var_f y.
Proof. intros. simpl. destruct (y == x). done. auto. Qed.

Hint Rewrite subst_tm_tm_var : subst.
Hint Rewrite subst_tm_tm_open_tm_wrt_tm : subst.

(* --------------------------------------------------- *)
(* application tactics for binding forms *)

Ltac fresh_apply_Grade x := 
  match goal with 
      | [ |- Grade ?P ?psi (a_Pi ?psi2 ?a ?b) ] => pick fresh x and apply G_Pi
      | [ |- Grade ?P ?psi (a_WSigma ?psi2 ?a ?b) ] => pick fresh x and apply G_WSigma
      | [ |- Grade ?P ?psi (a_SSigma ?psi2 ?a ?b) ] => pick fresh x and apply G_SSigma
      | [ |- Grade ?P ?psi (a_Abs ?psi2 ?b) ] => pick fresh x and apply G_Abs
      | [ |- Grade ?P ?psi (a_LetPair ?psi2 ?a ?b) ] => pick fresh x and apply G_LetPair
    end.

Ltac fresh_apply_GEq x := 
  match goal with 
      | [ |- GEq ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply GEq_Pi
      | [ |- GEq ?P ?psi (a_WSigma ?psi2 ?a ?b) (a_WSigma ?psi3 ?a3 ?b3) ] => pick fresh x and apply GEq_WSigma
      | [ |- GEq ?P ?psi (a_SSigma ?psi2 ?a ?b) (a_SSigma ?psi3 ?a2 ?b2) ] => pick fresh x and apply GEq_SSigma
      | [ |- GEq ?P ?psi (a_Abs ?psi2 ?b) (a_Abs ?psi3 ?b3) ] => pick fresh x and apply GEq_Abs
      | [ |- GEq ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_LetPair ?psi3 ?a2 ?b2)  ] => pick fresh x and apply GEq_LetPair
    end.

Ltac fresh_apply_DefEq x := 
  match goal with 
      | [ |- DefEq ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply Eq_Pi
      | [ |- DefEq ?P ?psi (a_WSigma ?psi2 ?a ?b) (a_WSigma ?psi3 ?a3 ?b3) ] => pick fresh x and apply Eq_WSigma
      | [ |- DefEq ?P ?psi (a_SSigma ?psi2 ?a ?b) (a_SSigma ?psi3 ?a2 ?b2) ] => pick fresh x and apply Eq_SSigma
      | [ |- DefEq ?P ?psi (a_Abs ?psi2 ?b) (a_Abs ?psi3 ?b3) ] => pick fresh x and apply Eq_Abs
      | [ |- DefEq ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_LetPair ?psi3 ?a2 ?b2)  ] => pick fresh x and apply Eq_LetPair
    end.

Ltac fresh_apply_Par x := 
  match goal with 
      | [ |- Par ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply Par_Pi
      | [ |- Par ?P ?psi (a_WSigma ?psi2 ?a ?b) (a_WSigma ?psi3 ?a3 ?b3) ] => pick fresh x and apply Par_WSigma
      | [ |- Par ?P ?psi (a_SSigma ?psi2 ?a ?b) (a_SSigma ?psi3 ?a2 ?b2) ] => pick fresh x and apply Par_SSigma
      | [ |- Par ?P ?psi (a_Abs ?psi2 ?b) (a_Abs ?psi3 ?b3) ] => pick fresh x and apply Par_Abs
      | [ |- Par ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_App ?a1 ?phi2 ?a2)  ] => pick fresh x and apply Par_WPairBeta
      | [ |- Par ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_LetPair ?psi3 ?a2 ?b2)  ] => pick fresh x and apply Par_LetPair
    end.

Ltac fresh_apply_Typing x := 
  match goal with 
      | [ |- Typing ?P ?psi (a_Pi ?psi2 ?a ?b) _ ] => pick fresh x and apply T_Pi
      | [ |- Typing ?P ?psi (a_WSigma ?psi2 ?a ?b) _ ] => pick fresh x and apply T_WSigma
      | [ |- Typing ?P ?psi (a_SSigma ?psi2 ?a ?b) _ ] => pick fresh x and apply T_SSigma
      | [ |- Typing ?P ?psi (a_Abs ?psi2 ?b) _ ] => pick fresh x and apply T_Abs
      | [ |- Typing ?P ?psi (a_LetPair ?psi2 ?a ?b) _ ] => pick fresh x and apply T_LetPair
      | [ |- Typing ?P ?psi (a_Case ?psi2 ?a ?b1 ?b2) _ ] => pick fresh x and apply T_Case
    end.

(* ------------------------------------------------- *)
(* Some of the judgements are not very syntax directed in the cases of App, Wpair and SPair.
   In each of these cases, the first constructor handles the "relevent" case, the second, 
   the "irrelevelent" case. 
*)


Ltac eapply_GradeIrrel := 
  match goal with 
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_App ?a ?psi0 ?b) ] => eapply G_AppIrrel
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_WPair ?a ?psi0 ?b) ] => eapply G_WPairIrrel
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_SPair ?a ?psi0 ?b) ] => eapply G_SPairIrrel
    end.


Ltac eapply_DefEqIrrel := 
  match goal with 
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_App ?a ?psi0 ?b) (a_App ?c ?psi0 ?d) ] => eapply Eq_AppIrrel
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_WPair ?a ?psi0 ?b) (a_WPair ?c ?psi0 ?d) ] => eapply Eq_WPairIrrel
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_SPair ?a ?psi0 ?b) (a_SPair ?c ?psi0 ?d) ] => eapply Eq_SPairIrrel
    end.


Ltac eapply_ParIrrel := 
  match goal with 
      | [ H : not (?psi0 <= ?psi) |- 
         Par ?P ?psi (a_App ?a ?psi0 ?b) (open_tm_wrt_tm ?c ?d) ] => eapply Par_AppBetaIrrel
      | [ H : not (?psi0 <= ?psi) |- 
         Par ?P ?psi (a_App ?a ?psi0 ?b) (a_App ?c ?psi0 ?d) ] => eapply Par_AppIrrel
      | [ H : not (?psi0 <= ?psi) |- 
         Par ?P ?psi (a_WPair ?a ?psi0 ?b) (a_WPair ?c ?psi0 ?d) ] => eapply Par_WPairIrrel
      | [ H : not (?psi0 <= ?psi) |- 
         Par ?P ?psi (a_SPair ?a ?psi0 ?b) (a_SPair ?c ?psi0 ?d) ] => eapply Par_SPairIrrel
    end.


(* ------------------------------------------------- *)

(* Inversion for a syntax-directed judgement. *)

Ltac invert_Grade := 
  match goal with 
      | [ H : Grade ?P ?psi (a_Var_f ?x) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Pi ?psi2 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_WSigma ?psi2 ?a ?b)  |- _  ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_SSigma ?psi2 ?a ?b)  |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Abs ?psi2 ?b) |- _  ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_LetPair ?psi2 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_App ?a ?psi1 ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Sum ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Inj1 ?a ) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Inj2 ?a ) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Case ?psi1 ?a ?b1 ?b2) |- _ ] => inversion H ; clear H  
      | [ H : Grade ?P ?psi (a_WPair ?a ?psi1 ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_SPair ?a ?psi1 ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Proj1 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Proj2 ?a ?b) |- _ ] => inversion H ; clear H
    end.
