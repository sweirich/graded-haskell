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

Scheme Grade_ind' := Induction for Grade Sort Prop
   with CGrade_ind'   := Induction for CGrade Sort Prop.

Combined Scheme CGrade_Grade_mutual
  from CGrade_ind', Grade_ind'.

Scheme Par_ind' := Induction for Par Sort Prop
   with CPar_ind'   := Induction for CPar Sort Prop.

Combined Scheme CPar_Par_mutual
  from CPar_ind', Par_ind'.

Scheme DefEq_ind' := Induction for DefEq Sort Prop
   with CDefEq_ind'   := Induction for CDefEq Sort Prop.

Combined Scheme CDefEq_DefEq_mutual
  from CDefEq_ind', DefEq_ind'.



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
      | [ |- Grade ?P ?psi (a_Abs ?psi2 ?A ?b) ] => pick fresh x and apply G_Abs
      | [ |- Grade ?P ?psi (a_LetPair ?psi2 ?a ?b) ] => pick fresh x and apply G_LetPair
    end.

Ltac fresh_apply_GEq x := 
  match goal with 
      | [ |- GEq ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply GEq_Pi
      | [ |- GEq ?P ?psi (a_WSigma ?psi2 ?a ?b) (a_WSigma ?psi3 ?a3 ?b3) ] => pick fresh x and apply GEq_WSigma
      | [ |- GEq ?P ?psi (a_SSigma ?psi2 ?a ?b) (a_SSigma ?psi3 ?a2 ?b2) ] => pick fresh x and apply GEq_SSigma
      | [ |- GEq ?P ?psi (a_Abs ?psi2 ?A1 ?b) (a_Abs ?psi3 ?A2 ?b3) ] => pick fresh x and apply GEq_Abs
      | [ |- GEq ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_LetPair ?psi3 ?a2 ?b2)  ] => pick fresh x and apply GEq_LetPair
    end.

Ltac fresh_apply_DefEq x := 
  match goal with 
      | [ |- DefEq ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply Eq_Pi
      | [ |- DefEq ?P ?psi (a_WSigma ?psi2 ?a ?b) (a_WSigma ?psi3 ?a3 ?b3) ] => pick fresh x and apply Eq_WSigma
      | [ |- DefEq ?P ?psi (a_SSigma ?psi2 ?a ?b) (a_SSigma ?psi3 ?a2 ?b2) ] => pick fresh x and apply Eq_SSigma
      | [ |- DefEq ?P ?psi (a_Abs ?psi2 ?A1 ?b) (a_Abs ?psi3 ?A2 ?b3) ] => pick fresh x and apply Eq_Abs
      | [ |- DefEq ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_LetPair ?psi3 ?a2 ?b2)  ] => pick fresh x and apply Eq_LetPair
    end.

Ltac fresh_apply_Par x := 
  match goal with 
      | [ |- Par ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply Par_Pi
      | [ |- Par ?P ?psi (a_WSigma ?psi2 ?a ?b) (a_WSigma ?psi3 ?a3 ?b3) ] => pick fresh x and apply Par_WSigma
      | [ |- Par ?P ?psi (a_SSigma ?psi2 ?a ?b) (a_SSigma ?psi3 ?a2 ?b2) ] => pick fresh x and apply Par_SSigma
      | [ |- Par ?P ?psi (a_Abs ?psi2 ?A ?b) (a_Abs ?psi3 ?A2 ?b3) ] => pick fresh x and apply Par_Abs
      | [ |- Par ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_App ?a1 ?phi2 ?a2)  ] => pick fresh x and apply Par_WPairBeta
      | [ |- Par ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_LetPair ?psi3 ?a2 ?b2)  ] => pick fresh x and apply Par_LetPair
    end.

Ltac fresh_apply_Typing x := 
  match goal with 
      | [ |- Typing ?P ?psi (a_Pi ?psi2 ?a ?b) _ ] => pick fresh x and apply T_Pi
      | [ |- Typing ?P ?psi (a_WSigma ?psi2 ?a ?b) _ ] => pick fresh x and apply T_WSigma
      | [ |- Typing ?P ?psi (a_SSigma ?psi2 ?a ?b) _ ] => pick fresh x and apply T_SSigma
      | [ |- Typing ?P ?psi (a_Abs ?psi2 ?A ?b) _ ] => pick fresh x and apply T_Abs
      | [ |- Typing ?P ?psi (a_LetPair ?psi2 ?a ?b) _ ] => pick fresh x and apply T_LetPair
      | [ |- Typing ?P ?psi (a_Case ?psi2 ?a ?b1 ?b2) _ ] => pick fresh x and apply T_Case
    end.

(* ------------------------------------------------- *)
(*
*)


Ltac eapply_GradeIrrel := 
  match goal with 
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_App ?a ?psi0 ?b) ] => eapply G_App;  [idtac|eapply CG_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_WPair ?a ?psi0 ?b) ] => eapply G_WPair;  [idtac|eapply CG_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_SPair ?a ?psi0 ?b) ] => eapply G_SPair;  [idtac|eapply CG_Nleq]
    end.


Ltac eapply_DefEqIrrel := 
  match goal with 
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_App ?a ?psi0 ?b) (a_App ?c ?psi0 ?d) ] => eapply Eq_App;  [idtac|eapply CEq_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_WPair ?a ?psi0 ?b) (a_WPair ?c ?psi0 ?d) ] => eapply Eq_WPair;  [idtac|eapply CEq_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_SPair ?a ?psi0 ?b) (a_SPair ?c ?psi0 ?d) ] => eapply Eq_SPair;  [idtac|eapply CEq_Nleq]
    end.


Ltac eapply_ParIrrel := 
  match goal with 
      | [ H : not (?psi0 <= ?psi) |- 
         Par ?P ?psi (a_App ?a ?psi0 ?b) (open_tm_wrt_tm ?c ?d) ] => eapply Par_AppBeta;  [idtac|eapply CPar_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         Par ?P ?psi (a_App ?a ?psi0 ?b) (a_App ?c ?psi0 ?d) ] => eapply Par_App;  [idtac|eapply CPar_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         Par ?P ?psi (a_WPair ?a ?psi0 ?b) (a_WPair ?c ?psi0 ?d) ] => eapply Par_WPair;  [idtac|eapply CPar_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         Par ?P ?psi (a_SPair ?a ?psi0 ?b) (a_SPair ?c ?psi0 ?d) ] => eapply Par_SPair;  [idtac|eapply CPar_Nleq]
    end.


(* ------------------------------------------------- *)

(* Inversion for a syntax-directed judgement. *)

Ltac invert_Grade := 
  match goal with 
      | [ H : Grade ?P ?psi (a_Var_f ?x) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Pi ?psi2 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_WSigma ?psi2 ?a ?b)  |- _  ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_SSigma ?psi2 ?a ?b)  |- _ ] => inversion H ; clear H
      | [ H : Grade ?P ?psi (a_Abs ?psi2 ?A ?b) |- _  ] => inversion H ; clear H
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


Ltac invert_GEq := 
  match goal with 
      | [ H : GEq ?P ?psi (a_Var_f ?x) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_Pi ?psi2 ?a ?b) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_WSigma ?psi2 ?a ?b)  _ |- _  ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_SSigma ?psi2 ?a ?b)  _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_Abs ?psi2 ?A ?b) _ |- _  ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_LetPair ?psi2 ?a ?b) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_App ?a ?psi1 ?b) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_Sum ?a ?b) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_Inj1 ?a ) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_Inj2 ?a ) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_Case ?psi1 ?a ?b1 ?b2) _ |- _ ] => inversion H ; clear H  
      | [ H : GEq ?P ?psi (a_WPair ?a ?psi1 ?b) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_SPair ?a ?psi1 ?b) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_Proj1 ?a ?b) _ |- _ ] => inversion H ; clear H
      | [ H : GEq ?P ?psi (a_Proj2 ?a ?b) _ |- _ ] => inversion H ; clear H
    end.

Ltac invert_lc := 
  match goal with 
      | [ H : lc_tm (a_Var_f ?x) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_Pi ?psi2 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_WSigma ?psi2 ?a ?b)  |- _  ] => inversion H ; clear H
      | [ H : lc_tm (a_SSigma ?psi2 ?a ?b)  |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_Abs ?psi2 ?A ?b) |- _  ] => inversion H ; clear H
      | [ H : lc_tm (a_LetPair ?psi2 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_App ?a ?psi1 ?b) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_Sum ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_Inj1 ?a ) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_Inj2 ?a ) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_Case ?psi1 ?a ?b1 ?b2) |- _ ] => inversion H ; clear H  
      | [ H : lc_tm (a_WPair ?a ?psi1 ?b) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_SPair ?a ?psi1 ?b) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_Proj1 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : lc_tm (a_Proj2 ?a ?b) |- _ ] => inversion H ; clear H
    end.



(* -------------------------------------------------------- *)

(* Local closure: we know that Ott produced relations are always locally closed. So it does not 
   hurt to axiomatize this fact. *)


Lemma CGrade_Grade_lc : 
  (forall P phi phi0 a,
  CGrade P phi phi0 a -> lc_tm a) /\
  (forall P phi a,
  Grade P phi a -> lc_tm a).
Proof. 
  eapply CGrade_Grade_mutual.
  all: intros; split_hyp; eauto.
Qed.

Lemma Grade_lc : forall {P psi a}, Grade P psi a -> lc_tm a.
Proof. intros. move: CGrade_Grade_lc => [h1 h2]. move: (h2 _ _ _ H) => h3. auto. Qed.
Lemma CGrade_lc : forall {P psi phi a}, CGrade P psi phi a -> lc_tm a.
Proof. intros. move: CGrade_Grade_lc => [h1 h2]. move: (h1 _ _ _ _ H) => h3. auto. Qed.


Lemma CEq_GEq_lc : 
  (forall P phi phi0 a b,
  CEq P phi phi0 a b -> lc_tm a /\ lc_tm b) /\
  (forall P phi a b,
  GEq P phi a b -> lc_tm a /\ lc_tm b).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; split_hyp; split; eauto.
  all: pick fresh x; repeat spec x; split_hyp.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
Qed.

Lemma GEq_lc1 : forall {W a psi b}, GEq W psi a b -> lc_tm a.
Proof. intros. move: CEq_GEq_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma GEq_lc2 : forall {W a psi b}, GEq W psi a b -> lc_tm b.
Proof. intros. move: CEq_GEq_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CEq_lc1 : forall {W a psi phi b}, CEq W psi phi a b -> lc_tm a.
Proof. intros. move: CEq_GEq_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CEq_lc2 : forall {W a psi phi b}, CEq W psi phi a b -> lc_tm b.
Proof. intros. move: CEq_GEq_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.

Lemma Step_lc1 : forall {a b}, Step a b -> lc_tm a.
Proof. intros. induction H; eauto. Qed.

Lemma Step_lc2 : forall {a b}, Step a b -> lc_tm b.
Proof. intros. induction H; eauto. 
       all: invert_lc.
       eapply lc_body_tm_wrt_tm; eauto.
       eauto.
       econstructor; eauto.
       eapply lc_body_tm_wrt_tm; eauto.
Qed.


Lemma CDefEq_DefEq_lc : 
  (forall P phi phi0 a b,
  CDefEq P phi phi0 a b -> lc_tm a /\ lc_tm b) /\
  (forall P phi a b,
  DefEq P phi a b -> lc_tm a /\ lc_tm b).
Proof.
  eapply CDefEq_DefEq_mutual.
  all: intros; split_hyp; split; repeat invert_lc; eauto using Grade_lc.
  all: try solve [eapply lc_body_tm_wrt_tm; eauto using Grade_lc].
  all: pick fresh x; repeat spec x; split_hyp.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
  rewrite (subst_tm_tm_intro x); auto.
  eapply subst_tm_tm_lc_tm; auto.
  rewrite (subst_tm_tm_intro x); auto.
  eapply subst_tm_tm_lc_tm; auto.
Qed.

Lemma DefEq_lc1 : forall {W a psi b}, DefEq W psi a b -> lc_tm a.
Proof. intros. move: CDefEq_DefEq_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma DefEq_lc2 : forall {W a psi b}, DefEq W psi a b -> lc_tm b.
Proof. intros. move: CDefEq_DefEq_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CDefEq_lc1 : forall {W a psi phi b}, CDefEq W psi phi a b -> lc_tm a.
Proof. intros. move: CDefEq_DefEq_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CDefEq_lc2 : forall {W a psi phi b}, CDefEq W psi phi a b -> lc_tm b.
Proof. intros. move: CDefEq_DefEq_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.



Lemma Typing_lc1 : 
  (forall P phi a b,
  Typing P phi a b -> lc_tm a).
Proof.
  induction 1.
  all: intros; split_hyp; repeat invert_lc; eauto using Grade_lc.  
  pick fresh x; repeat spec x.
  pick fresh y; repeat spec y.
  eapply lc_a_LetPair_exists; eauto.
Qed.

Lemma CTyping_lc1 : forall W q a A, CTyping W q a A -> lc_tm a. 
Proof. intros. induction H; eauto using Typing_lc1. Qed.


Lemma CPar_Par_lc : 
  (forall P phi phi0 a b,
  CPar P phi phi0 a b -> lc_tm a /\ lc_tm b) /\
  (forall P phi a b,
  Par P phi a b -> lc_tm a /\ lc_tm b).
Proof.
  eapply CPar_Par_mutual.
  all: intros; split_hyp; split; repeat invert_lc; eauto using Grade_lc.
  all: try solve [eapply lc_body_tm_wrt_tm; eauto using Grade_lc].  
  all: pick fresh x; repeat spec x; split_hyp.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  econstructor; eauto.
  rewrite (subst_tm_tm_intro x); auto.
  eapply subst_tm_tm_lc_tm; auto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
Qed.

Lemma Par_lc1 : forall {W a psi b}, Par W psi a b -> lc_tm a.
Proof. intros. move: CPar_Par_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma Par_lc2 : forall {W a psi b}, Par W psi a b -> lc_tm b.
Proof. intros. move: CPar_Par_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CPar_lc1 : forall {W a psi phi b}, CPar W psi phi a b -> lc_tm a.
Proof. intros. move: CPar_Par_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CPar_lc2 : forall {W a psi phi b}, CPar W psi phi a b -> lc_tm b.
Proof. intros. move: CPar_Par_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.



Lemma MultiPar_lc1 : forall {G a psi a'}, MultiPar G psi a a' -> lc_tm a.
Proof. induction 1. eauto using Grade_lc. eauto using Par_lc1. Qed.
Lemma MultiPar_lc2 : forall {G a psi a'}, MultiPar G psi a a' -> lc_tm a'.
Proof. induction 1; eauto using Grade_lc. Qed.

Lemma ValueType_lc : forall {A}, ValueType A -> lc_tm A.
Proof. induction 1; eauto. Qed.

Lemma Joins_lc1 : forall {G a psi a'}, Joins G psi a a' -> lc_tm a.
Proof. induction 1; eauto using MultiPar_lc1. Qed.
Lemma Joins_lc2 : forall {G a psi a'}, Joins G psi a a' -> lc_tm a'.
Proof. induction 1; eauto using MultiPar_lc1. Qed.

Lemma CMultiPar_lc1 : forall {G a psi psi0 a'}, CMultiPar G psi psi0 a a' -> lc_tm a.
Proof. induction 1; eauto using MultiPar_lc1. Qed.

Lemma CMultiPar_lc2 : forall {G a psi psi0 a'}, CMultiPar G psi psi0 a a' -> lc_tm a'.
Proof. induction 1; eauto using MultiPar_lc2. Qed.

Lemma CJoins_lc1 : forall {G a psi phi a'}, CJoins G psi phi a a' -> lc_tm a.
Proof. induction 1; eauto using Joins_lc1. Qed.

Lemma CJoins_lc2 : forall {G a psi phi a'}, CJoins G psi phi a a' -> lc_tm a'.
Proof. induction 1; eauto using Joins_lc2. Qed.
