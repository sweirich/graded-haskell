Require Export ssreflect.
Require Export Qual.Qualitative_ott.
Require Import Qual.Qualitative_inf.
Require Export Metalib.LibTactics.
Require Export Coq.Program.Equality.
Require Export Qual.classes.

Set Implicit Arguments.
Open Scope grade_scope.
Open Scope general_if_scope.

(* type classes *)

#[local] Transparent Syntax_tm.
#[export] Instance SyntaxTheory_tm : SyntaxTheory tm := {
    fv_close := fv_tm_tm_close_tm_wrt_tm;
    close_inj := close_tm_wrt_tm_inj
}.
#[local] Transparent Subst_tm.
#[export] Instance Subst_tm : SubstTheory tm tm a_Var_f := { 
    subst_close := subst_tm_tm_close_tm_wrt_tm;
    fv_open_lower := fv_tm_tm_open_tm_wrt_tm_lower;
    fv_open_upper := fv_tm_tm_open_tm_wrt_tm_upper;
    open_close := open_tm_wrt_tm_close_tm_wrt_tm;
    subst_intro := subst_tm_tm_intro;
    subst_open_var := subst_tm_tm_open_tm_wrt_tm_var;
    subst_fresh_eq := subst_tm_tm_fresh_eq;
    open_inj := open_tm_wrt_tm_inj;
    subst_lc := subst_tm_tm_lc_tm;
    subst_spec := subst_tm_tm_spec;
    size_open_var := size_tm_open_tm_wrt_tm_var
}.

#[export] Instance SubstOpen_tm : SubstOpenTheory tm tm a_Var_f := {
    subst_open := subst_tm_tm_open_tm_wrt_tm;
}.

(*
    a_TyUnit : tm
  | a_TmUnit : tm
  | a_Type : sort -> tm
  | a_Sum : tm -> tm -> tm
  | a_Inj1 : tm -> tm
  | a_Inj2 : tm -> tm
  | a_Case : grade -> tm -> tm -> tm -> tm
  | a_WSigma : grade -> tm -> tm -> tm
  | a_WPair : tm -> grade -> tm -> tm
  | a_LetPair : grade -> tm -> tm -> tm
*)


(* This is only a small fraction of the lemmas that we need to have a full rewriting 
   definition for the syntactic operations. *)

Lemma fv_tm_a_Var_b : forall (m: nat), fv (a_Var_b m) = {}. 
Proof. reflexivity. Qed.
Lemma fv_tm_a_Var_f : forall (x:atom), fv (a_Var_f x) = {{x}}.
Proof. reflexivity. Qed.
Lemma fv_tm_a_Abs : forall h A (e: tm), fv (a_Abs h A e) = fv A \u fv e.
Proof. reflexivity. Qed.
Lemma fv_tm_a_Pi : forall h A (e: tm), fv (a_Pi h A e) = fv A \u fv e.
Proof. reflexivity. Qed.
Lemma fv_tm_a_App : forall g (e1 : tm) (e2: tm), fv (a_App e1 g e2) = fv e1 `union` fv e2.
Proof. reflexivity. Qed.
Lemma fv_tm_a_TyUnit : fv (a_TyUnit) = {}.
Proof. reflexivity. Qed.
Lemma fv_tm_a_TmUnit : fv (a_TmUnit) = {}.
Proof. reflexivity. Qed.
Lemma fv_tm_a_Type : forall s, fv (a_Type s) = {}.
Proof. reflexivity. Qed.
Lemma fv_tm_a_Sum : forall a b, fv (a_Sum a b) = fv a \u fv b.
Proof. reflexivity. Qed.
Lemma fv_tm_a_Inj1 : forall a, fv (a_Inj1 a) = fv a.
Proof. reflexivity. Qed.
Lemma fv_tm_a_Inj2 : forall a, fv (a_Inj2 a) = fv a.
Proof. reflexivity. Qed.
Lemma fv_tm_a_Case : forall g a b c, fv (a_Case g a b c) = fv a \u fv b \u fv c.
Proof. reflexivity. Qed.
Lemma fv_tm_a_WSigma : forall g a b, fv (a_WSigma g a b) = fv a \u fv b. 
Proof. reflexivity. Qed.
Lemma fv_tm_a_WPair : forall a g b, fv (a_WPair a g b) = fv a \u fv b.
Proof. reflexivity. Qed.
Lemma fv_tm_a_LetPair : forall g a b, fv (a_LetPair g a b) = fv a \u fv b.
Proof. reflexivity. Qed.

#[export] Hint Rewrite fv_tm_a_Var_b fv_tm_a_Var_f fv_tm_a_Abs fv_tm_a_Pi fv_tm_a_App
  fv_tm_a_TyUnit fv_tm_a_TmUnit fv_tm_a_Type fv_tm_a_Sum fv_tm_a_Inj1 
  fv_tm_a_Inj2 fv_tm_a_Case fv_tm_a_WSigma fv_tm_a_WPair fv_tm_a_LetPair : fv.

Lemma close_tm_a_Var_b : forall x (m: nat) n,   close_rec n x (a_Var_b m) = a_Var_b m.
Proof. reflexivity. Qed.
Lemma close_tm_a_Var_f : forall (x1 x2:atom) n, close_rec n x1 (a_Var_f x2) = if (x1 == x2) then (a_Var_b n) else (a_Var_f x2).
Proof. reflexivity. Qed.
Lemma close_tm_a_Abs : forall g A (e: tm) x1 n, close_rec n x1 (a_Abs g A e) = a_Abs g (close_rec n x1 A) (close_rec (S n) x1 e).
Proof. reflexivity. Qed.
Lemma close_tm_a_App : forall g (e1 : tm) (e2: tm) x1 n, close_rec n x1 (a_App e1 g e2) = a_App (close_rec n x1 e1) g (close_rec n x1 e2).
Proof. reflexivity. Qed.
Lemma close_tm_a_Pi : forall g A (e: tm) x1 n, close_rec n x1 (a_Pi g A e) = a_Pi g (close_rec n x1 A) (close_rec (S n) x1 e).
Proof. reflexivity. Qed.
Lemma close_tm_a_WSigma : forall g A (e: tm) x1 n, close_rec n x1 (a_WSigma g A e) = a_WSigma g (close_rec n x1 A) (close_rec (S n) x1 e).
Proof. reflexivity. Qed.
Lemma close_tm_a_WPair : forall g A (e: tm) x1 n, close_rec n x1 (a_WPair A g e) = a_WPair (close_rec n x1 A) g (close_rec n x1 e).
Proof. reflexivity. Qed.




#[export] Hint Rewrite close_tm_a_Var_b close_tm_a_Var_f close_tm_a_Abs close_tm_a_App close_tm_a_Pi 
  close_tm_a_WSigma close_tm_a_WPair : close.

Lemma open_tm_a_Var_b : forall k (u:tm) nat, open_rec k u (a_Var_b nat) = match lt_eq_lt_dec nat k with
        | inleft (left _) => a_Var_b nat
        | inleft (right _) => u
        | inright _ => a_Var_b (nat - 1)
      end.
Proof. reflexivity. Qed.
Lemma open_tm_a_Var_f : forall k (u:tm) (x:atom), open_rec k u (a_Var_f x) = a_Var_f x.
Proof. reflexivity. Qed.

Lemma open_tm_a_Abs : forall k (u:tm) A g e, 
    open_rec k u (a_Abs g A e) = a_Abs g (open_rec k u A) (open_rec (S k) u e).
Proof. reflexivity. Qed. 
Lemma open_tm_a_App : forall k (u:tm) (e1 : tm) g (e2: tm), 
    open_rec k u (a_App e1 g e2) = a_App (open_rec k u e1) g (open_rec k u e2).
Proof. reflexivity. Qed. 
Lemma open_tm_a_Pi : forall k (u:tm) A g e, 
    open_rec k u (a_Pi g A e) = a_Pi g (open_rec k u A) (open_rec (S k) u e).
Proof. reflexivity. Qed. 
Lemma open_tm_a_WSigma : forall k (u:tm) A g e, 
    open_rec k u (a_WSigma g A e) = a_WSigma g (open_rec k u A) (open_rec (S k) u e).
Proof. reflexivity. Qed. 
Lemma open_tm_a_WPair : forall k (u:tm) A g e, 
    open_rec k u (a_WPair A g e) = a_WPair (open_rec k u A) g (open_rec k u e).
Proof. reflexivity. Qed. 

#[export] Hint Rewrite open_tm_a_Var_b open_tm_a_Var_f open_tm_a_Abs open_tm_a_App open_tm_a_Pi 
  open_tm_a_WSigma open_tm_a_WPair : open.

Lemma subst_tm_a_Var_b : forall (u:tm) (y:atom) (m: nat), 
    subst u y (a_Var_b m) = a_Var_b m.
Proof. reflexivity. Qed.
Lemma subst_tm_a_Var_f : forall (u:tm) (y:atom) (x:atom), 
    subst u y (a_Var_f x) = if x == y then u else a_Var_f x.
Proof. reflexivity. Qed.
Lemma subst_tm_a_Abs : forall (u:tm) (y:atom) g A (e: tm), 
    subst u y (a_Abs g A e) = a_Abs g (subst u y A) (subst u y e).
Proof. reflexivity. Qed.
Lemma subst_tm_a_App : forall (u:tm) (y:atom) (e1 : tm) g (e2: tm), 
    subst u y (a_App e1 g e2) = a_App (subst u y e1) g (subst u y e2).
Proof. reflexivity. Qed.
Lemma subst_tm_a_Pi : forall (u:tm) (y:atom) g A (e: tm), 
    subst u y (a_Pi g A e) = a_Pi g (subst u y A) (subst u y e).
Proof. reflexivity. Qed.
Lemma subst_tm_a_WSigma :  forall (u:tm) (y:atom) g A (e: tm), 
    subst u y (a_WSigma g A e) = a_WSigma g (subst u y A) (subst u y e).
Proof. reflexivity. Qed.

Lemma subst_tm_a_WPair :  forall (u:tm) (y:atom) g A (e: tm), 
    subst u y (a_WPair A g e) = a_WPair (subst u y A) g (subst u y e).
Proof. reflexivity. Qed.
Lemma subst_tm_a_LetPair :  forall (u:tm) (y:atom) g A (e: tm), 
    subst u y (a_LetPair g A e) = a_LetPair g (subst u y A) (subst u y e).
Proof. reflexivity. Qed.

Lemma subst_tm_a_SSigma :  forall (u:tm) (y:atom) g A (e: tm), 
    subst u y (a_SSigma g A e) = a_SSigma g (subst u y A) (subst u y e).
Proof. reflexivity. Qed.
Lemma subst_tm_a_SPair :  forall (u:tm) (y:atom) g A (e: tm), 
    subst u y (a_SPair A g e) = a_SPair (subst u y A) g (subst u y e).
Proof. reflexivity. Qed.
Lemma subst_tm_a_TmUnit : forall (u:tm) (y:atom), 
    subst u y a_TmUnit = a_TmUnit.
Proof. reflexivity. Qed.
Lemma subst_tm_a_TyUnit : forall (u:tm) (y:atom), 
    subst u y a_TyUnit = a_TyUnit.
Proof. reflexivity. Qed.
Lemma subst_tm_a_Type : forall (u:tm) (y:atom) s, 
    subst u y (a_Type s) = a_Type s.
Proof. reflexivity. Qed.

#[export] Hint Rewrite subst_tm_a_Var_b subst_tm_a_Abs subst_tm_a_App subst_tm_a_Pi
  subst_tm_a_WSigma subst_tm_a_WPair subst_tm_a_LetPair subst_tm_a_SSigma subst_tm_a_SPair
  subst_tm_a_TmUnit subst_tm_a_TyUnit subst_tm_a_Type : subst.

(* Note: we don't automatically rewrite subst_tm_a_Var_f 
   Instead, we break this into two rewriting rules for subst. *)

Lemma subst_var : forall a x, subst a x (a_Var_f x) = a.
Proof. intros. simpl. destruct (x == x) eqn:H; rewrite H. auto. done. Qed.
Lemma subst_var_neq : forall a x y, y <> x -> subst a x (a_Var_f y) = a_Var_f y.
Proof. intros. simpl. destruct (y == x) eqn:h; rewrite h. done. auto. Qed.

#[export] Hint Rewrite subst_var : subst.

(* This tactic looks for a variable substitution and does the case analysis
   for the two cases above. *)
Ltac substitution_var := 
  match goal with 
    [  b : binds _ _ _  |- context[subst ?a ?x0 (a_Var_f ?x)] ] => 
      destruct (x == x0); subst; 
      [ repeat rewrite subst_var;
        apply binds_mid_eq in b; try invert_equality; auto 
      | repeat rewrite subst_var_neq; 
        apply binds_remove_mid in b;
        auto ]
  | [ |- context[subst ?a ?x0 (a_Var_f ?x)] ] => 
      destruct (x == x0); subst; 
      [ repeat rewrite subst_var; auto
      | repeat rewrite subst_var_neq; auto ]
  end.



Open Scope nat_scope.

Lemma size_tm_a_Var_b : forall (m: nat), 
    size (a_Var_b m) = 1.
Proof. reflexivity. Qed.
Lemma size_tm_a_Var_f : forall (x:atom), 
    size (a_Var_f x) = 1.
Proof. reflexivity. Qed.
Lemma size_tm_a_Abs : forall  g A (e: tm), 
    size (a_Abs g A e) = 2 + (size A) + (size e).
Proof. reflexivity. Qed.
Lemma size_tm_a_App : forall  (e1 : tm) g (e2: tm), 
    size (a_App e1 g e2) = 1 + (size e1) + 1 + (size e2).
Proof. reflexivity. Qed.
Lemma size_tm_a_Pi : forall  g A (e: tm), 
    size (a_Pi g A e) = 2 + (size A) + (size e).
Proof. reflexivity. Qed.
Lemma size_tm_a_WSigma :  forall  g A (e: tm), 
    size (a_WSigma g A e) = 2 +  (size A) + (size e).
Proof. reflexivity. Qed.
Lemma size_tm_a_SSigma :  forall  g A (e: tm), 
    size (a_SSigma g A e) = 2 + (size A) + (size e).
Proof. reflexivity. Qed.
Lemma size_tm_a_LetPair :  forall  g A (e: tm), 
    size (a_LetPair g A e) = 2 + (size A) + (size e).
Proof. reflexivity. Qed.
Lemma size_tm_a_TmUnit :
    size a_TmUnit = 1.
Proof. reflexivity. Qed.
Lemma size_tm_a_TyUnit : 
    size a_TyUnit = 1.
Proof. reflexivity. Qed.
Lemma size_tm_a_Type : forall  s, 
    size (a_Type s) = 2.
Proof. reflexivity. Qed.
Lemma size_tm_a_WPair :  forall  g A (e: tm), 
    size (a_WPair A g e) = 1 + (size A) + 1 + (size e).
Proof. reflexivity. Qed.
Lemma size_tm_a_SPair :  forall  g A (e: tm), 
    size (a_SPair A g e) = 1 + (size A) + 1 + (size e).
Proof. reflexivity. Qed.

#[export] Hint Rewrite size_tm_a_Var_b size_tm_a_Var_f size_tm_a_Abs size_tm_a_App size_tm_a_Pi
  size_tm_a_WSigma size_tm_a_WPair size_tm_a_SSigma size_tm_a_LetPair size_tm_a_SSigma size_tm_a_SPair
  size_tm_a_TmUnit size_tm_a_TyUnit size_tm_a_Type : size.


(* ------------------------------------------------------- *)

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

(* ------------------------------------------------------- *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : context => dom x) in
  let D := gather_atoms_with (fun x => fv x) in
  let E := gather_atoms_with (fun x : econtext => dom x) in
  constr:(A \u B \u C \u D \u E).

(* -------------------------------------------- *)


(* -------------------------------------------- *)



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
  lazymatch goal with 
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_App ?a ?psi0 ?b) ] => eapply G_App;  [idtac|eapply CG_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_WPair ?a ?psi0 ?b) ] => eapply G_WPair;  [idtac|eapply CG_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         Grade ?P ?psi (a_SPair ?a ?psi0 ?b) ] => eapply G_SPair;  [idtac|eapply CG_Nleq]
    end.


Ltac eapply_DefEqIrrel := 
  lazymatch goal with 
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_App ?a ?psi0 ?b) (a_App ?c ?psi0 ?d) ] => eapply Eq_App;  [idtac|eapply CEq_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_WPair ?a ?psi0 ?b) (a_WPair ?c ?psi0 ?d) ] => eapply Eq_WPair;  [idtac|eapply CEq_Nleq]
      | [ H : not (?psi0 <= ?psi) |- 
         DefEq ?P ?psi (a_SPair ?a ?psi0 ?b) (a_SPair ?c ?psi0 ?d) ] => eapply Eq_SPair;  [idtac|eapply CEq_Nleq]
    end.


Ltac eapply_ParIrrel := 
  lazymatch goal with 
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
  lazymatch goal with 
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

Ltac invert_CGrade := 
    match goal with [ H : CGrade _ _ _ _ |- _ ] => inversion H; clear H end.


Ltac invert_GEq := 
  lazymatch goal with 
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

Ltac invert_CEq :=
   match goal with [ H : CEq _ _ _ _ _ |- _ ] => inversion H; clear H end.

(* ------------------------------------------------------------------------------- *)

(* Inversion lemmas to keep the "class"-based version of the lc relation. *)

Lemma lc_a_Pi_inversion : forall psi A B, 
    lc (a_Pi psi A B) -> lc A /\ (forall x, lc (open B (a_Var_f x))).
Proof. intros. inversion H. split; eauto. Qed.
Lemma lc_a_Abs_inversion : forall psi A B, 
    lc (a_Abs psi A B) -> lc A /\ (forall x, lc (open B (a_Var_f x))).
Proof. intros. inversion H. split; eauto. Qed.
Lemma lc_a_App_inversion : forall psi A B, 
    lc (a_App A psi B) -> lc A /\ lc B.
Proof. intros. inversion H. split; eauto. Qed.
Lemma lc_a_WSigma_inversion : forall psi A B, 
    lc (a_WSigma psi A B) -> lc A /\ (forall x, lc (open B (a_Var_f x))).
Proof. intros. inversion H. split; eauto. Qed.
Lemma lc_a_SSigma_inversion : forall psi A B, 
    lc (a_WSigma psi A B) -> lc A /\ (forall x, lc (open B (a_Var_f x))).
Proof. intros. inversion H. split; eauto. Qed.
Lemma lc_a_LetPair_inversion : forall psi a1 b1, 
    lc (a_LetPair psi a1 b1) -> lc a1 /\ (forall x, lc (open b1 (a_Var_f x))).
Proof. intros. inversion H. split; eauto. Qed.
Lemma lc_a_WPair_inversion : forall psi A B, 
    lc (a_WPair A psi B) -> lc A /\ lc B.
Proof. intros. inversion H. split; eauto. Qed.

Ltac invert_lc := 
  lazymatch goal with 
      | [ H : lc (a_Var_f ?x) |- _ ] => inversion H ; clear H
      | [ H : lc (a_Pi ?psi2 ?a ?b) |- _ ] => 
          apply lc_a_Pi_inversion in H; destruct H
      | [ H : lc (a_Abs ?psi2 ?A ?b) |- _  ] => 
          apply lc_a_Abs_inversion in H; destruct H
      | [ H : lc (a_App ?a ?psi1 ?b) |- _ ] => 
          apply lc_a_App_inversion in H; destruct H
      | [ H : lc (a_WSigma ?psi2 ?a ?b)  |- _  ] => 
          apply lc_a_WSigma_inversion in H; destruct H
      | [ H : lc (a_WPair ?a ?psi1 ?b) |- _ ] => 
          apply lc_a_WPair_inversion in H; destruct H
      | [ H : lc (a_LetPair ?psi2 ?a ?b) |- _ ] => 
          apply lc_a_LetPair_inversion in H; destruct H
      | [ H : lc (a_Sum ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : lc (a_Inj1 ?a ) |- _ ] => inversion H ; clear H
      | [ H : lc (a_Inj2 ?a ) |- _ ] => inversion H ; clear H
      | [ H : lc (a_Case ?psi1 ?a ?b1 ?b2) |- _ ] => inversion H ; clear H  
      | [ H : lc (a_SSigma ?psi2 ?a ?b)  |- _ ] => 
          apply lc_a_SSigma_inversion in H; destruct H
      | [ H : lc (a_SPair ?a ?psi1 ?b) |- _ ] => inversion H ; clear H
      | [ H : lc (a_Proj1 ?a ?b) |- _ ] => inversion H ; clear H
      | [ H : lc (a_Proj2 ?a ?b) |- _ ] => inversion H ; clear H
    end.


(* "lc" version of constructors *)

Lemma lc_a_Pi_exists : forall x (psi:grade) (A B:tm),
     (lc A) ->
      lc (open B (a_Var_f x))  ->
     (lc (a_Pi psi A B)).
Proof. intros. eapply lc_a_Pi_exists; eauto. Qed.  
Lemma lc_a_Abs_exists : forall x (psi:grade) (A a:tm),
     (lc_tm A) ->
     lc_tm (open a (a_Var_f x))  ->
     (lc (a_Abs psi A a)). 
Proof. intros. eapply lc_a_Abs_exists; eauto. Qed.
Lemma lc_a_App : forall (a:tm) (psi:grade) (b:tm),
     (lc a) ->
     (lc b) ->
     (lc (a_App a psi b)).
Proof. intros. econstructor; eauto. Qed.
Lemma lc_a_Type : forall (s:sort),
     (lc (a_Type s)).
Proof. intros. econstructor; eauto. Qed.
Lemma lc_a_Var_f : forall (x:tmvar),
     (lc (a_Var_f x)).
Proof. intros. econstructor; eauto. Qed.
Lemma lc_a_TmUnit : (lc (a_TmUnit)).
Proof. intros. econstructor; eauto. Qed.
Lemma lc_a_TyUnit : (lc (a_TyUnit)).
Proof. intros. econstructor; eauto. Qed.


Lemma lc_a_WSigma_exists : forall x (psi:grade) (A B:tm),
     (lc A) ->
      lc (open B (a_Var_f x))  ->
     (lc (a_WSigma psi A B)).
Proof. intros. eapply lc_a_WSigma_exists; eauto. Qed.  
Lemma lc_a_WPair : forall (a:tm) (psi:grade) (b:tm),
     (lc a) ->
     (lc b) ->
     (lc (a_WPair a psi b)).
Proof. intros. econstructor; eauto. Qed.
Lemma lc_a_LetPair_exists :  forall (x1 : tmvar) (psi1 : grade) (a1 b1 : tm),
       lc a1 -> lc (open b1 (a_Var_f x1)) -> lc (a_LetPair psi1 a1 b1).
Proof. intros. eapply lc_a_LetPair_exists; eauto. Qed.


#[export] Hint Resolve lc_a_Pi_exists lc_a_Abs_exists lc_a_App 
 lc_a_WSigma_exists lc_a_WPair lc_a_LetPair_exists : lc.
#[export] Hint Resolve lc_a_Type lc_a_Var_f lc_a_TmUnit lc_a_TyUnit : lc.

Lemma CGrade_Grade_lc : 
  (forall P phi phi0 a,
  CGrade P phi phi0 a -> lc a) /\
  (forall P phi a,
  Grade P phi a -> lc a).
Proof. 
  eapply CGrade_Grade_mutual.
  all: intros; split_hyp; eauto with lc.
  all: pick fresh y; repeat spec y; eauto with lc.
Admitted.

Lemma Grade_lc : forall {P psi a}, Grade P psi a -> lc a.
Proof. intros. move: CGrade_Grade_lc => [h1 h2]. move: (h2 _ _ _ H) => h3. auto. Qed.
Lemma CGrade_lc : forall {P psi phi a}, CGrade P psi phi a -> lc a.
Proof. intros. move: CGrade_Grade_lc => [h1 h2]. move: (h1 _ _ _ _ H) => h3. auto. Qed.


Lemma CEq_GEq_lc : 
  (forall P phi phi0 a b,
  CEq P phi phi0 a b -> lc a /\ lc b) /\
  (forall P phi a b,
  GEq P phi a b -> lc a /\ lc b).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; split_hyp; split; eauto with lc.
  all: pick fresh x; repeat spec x; split_hyp.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
Admitted.
(*
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
Qed. *)

Lemma GEq_lc1 : forall {W a psi b}, GEq W psi a b -> lc a.
Proof. intros. move: CEq_GEq_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma GEq_lc2 : forall {W a psi b}, GEq W psi a b -> lc b.
Proof. intros. move: CEq_GEq_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CEq_lc1 : forall {W a psi phi b}, CEq W psi phi a b -> lc a.
Proof. intros. move: CEq_GEq_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CEq_lc2 : forall {W a psi phi b}, CEq W psi phi a b -> lc b.
Proof. intros. move: CEq_GEq_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.

Lemma Step_lc1 : forall {a b}, Step a b -> lc a.
Proof. intros. induction H; eauto with lc. Admitted.

Lemma Step_lc2 : forall {a b}, Step a b -> lc b.
Proof. intros. induction H; eauto with lc. 
       - invert_lc.
         eapply lc_body; eauto.
Admitted.


Lemma CDefEq_DefEq_lc : 
  (forall P phi phi0 a b,
  CDefEq P phi phi0 a b -> lc a /\ lc b) /\
  (forall P phi a b,
  DefEq P phi a b -> lc a /\ lc b).
Proof.
  eapply CDefEq_DefEq_mutual.
  all: intros; split_hyp; split; repeat invert_lc; eauto using Grade_lc; eauto with lc.
  all: try solve [eapply lc_body; eauto using Grade_lc].
  all: pick fresh x; repeat spec x; split_hyp.
  all: try (rewrite (subst_intro x); auto;
            eapply subst_lc; auto).
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
Admitted.
(* eapply lc_a_WSigma_exists; eauto. 
  eapply lc_a_WSigma_exists; eauto. 
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
Qed. *)

Lemma DefEq_lc1 : forall {W a psi b}, DefEq W psi a b -> lc a.
Proof. intros. move: CDefEq_DefEq_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma DefEq_lc2 : forall {W a psi b}, DefEq W psi a b -> lc b.
Proof. intros. move: CDefEq_DefEq_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CDefEq_lc1 : forall {W a psi phi b}, CDefEq W psi phi a b -> lc a.
Proof. intros. move: CDefEq_DefEq_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CDefEq_lc2 : forall {W a psi phi b}, CDefEq W psi phi a b -> lc b.
Proof. intros. move: CDefEq_DefEq_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.



Lemma Typing_lc1 : 
  (forall P phi a b,
  Typing P phi a b -> lc a).
Proof.
  induction 1.
  all: intros; split_hyp; repeat invert_lc; eauto using Grade_lc with lc.
  all: pick fresh x; repeat spec x.
  all: pick fresh y; repeat spec y.
  all: eauto with lc.
Admitted. 

Lemma CTyping_lc1 : forall W q a A, CTyping W q a A -> lc a. 
Proof. intros. induction H; eauto using Typing_lc1. Qed.


Lemma CPar_Par_lc : 
  (forall P phi phi0 a b,
  CPar P phi phi0 a b -> lc a /\ lc b) /\
  (forall P phi a b,
  Par P phi a b -> lc a /\ lc b).
Proof.
  eapply CPar_Par_mutual.
  all: intros; split_hyp; split; repeat invert_lc; eauto using Grade_lc with lc.
  all: try solve [eapply lc_body; eauto using Grade_lc with lc].  
  all: pick fresh x; repeat spec x; split_hyp.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Pi_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_Abs_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
  eapply lc_a_WSigma_exists; eauto.
Admitted.
(*
  eapply lc_a_LetPair_exists; eauto.
  econstructor; eauto.
  rewrite (subst_tm_tm_intro x); auto.
  eapply subst_tm_tm_lc; auto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_LetPair_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
  eapply lc_a_SSigma_exists; eauto.
Qed. *)

Lemma Par_lc1 : forall {W a psi b}, Par W psi a b -> lc a.
Proof. intros. move: CPar_Par_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma Par_lc2 : forall {W a psi b}, Par W psi a b -> lc b.
Proof. intros. move: CPar_Par_lc => [h1 h2]. move: (h2 _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CPar_lc1 : forall {W a psi phi b}, CPar W psi phi a b -> lc a.
Proof. intros. move: CPar_Par_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.
Lemma CPar_lc2 : forall {W a psi phi b}, CPar W psi phi a b -> lc b.
Proof. intros. move: CPar_Par_lc => [h1 h2]. move: (h1 _ _ _ _ _ H) => h3. split_hyp. auto. Qed.



Lemma MultiPar_lc1 : forall {G a psi a'}, MultiPar G psi a a' -> lc a.
Proof. induction 1. eauto using Grade_lc. eauto using Par_lc1. Qed.
Lemma MultiPar_lc2 : forall {G a psi a'}, MultiPar G psi a a' -> lc a'.
Proof. induction 1; eauto using Grade_lc. Qed.

Lemma ValueType_lc : forall {A}, ValueType A -> lc A.
Proof. induction 1; eauto with lc. Admitted.

Lemma Joins_lc1 : forall {G a psi a'}, Joins G psi a a' -> lc a.
Proof. induction 1; eauto using MultiPar_lc1. Qed.
Lemma Joins_lc2 : forall {G a psi a'}, Joins G psi a a' -> lc a'.
Proof. induction 1; eauto using MultiPar_lc1. Qed.

Lemma CMultiPar_lc1 : forall {G a psi psi0 a'}, CMultiPar G psi psi0 a a' -> lc a.
Proof. induction 1; eauto using MultiPar_lc1. Qed.

Lemma CMultiPar_lc2 : forall {G a psi psi0 a'}, CMultiPar G psi psi0 a a' -> lc a'.
Proof. induction 1; eauto using MultiPar_lc2. Qed.

Lemma CJoins_lc1 : forall {G a psi phi a'}, CJoins G psi phi a a' -> lc a.
Proof. induction 1; eauto using Joins_lc1. Qed.

Lemma CJoins_lc2 : forall {G a psi phi a'}, CJoins G psi phi a a' -> lc a'.
Proof. induction 1; eauto using Joins_lc2. Qed.

(* ----------------------------------------- *)

#[global] Opaque Syntax_tm. 
#[global] Opaque Subst_tm.
#[global] Opaque SubstOpen_tm.
