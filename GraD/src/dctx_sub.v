Require Import ssreflect.
Require Import Coq.Classes.EquivDec.
Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.

Require Import Qtt.tactics.
Require Import Qtt.usage.
Require Import Qtt.dctx.


(* ----------------------------------------------------------------------- *)
(** **    Lemmas about the context, reflecting the usage structure         *)


(* ----------------------------------------------------------------- *)
(** *** ctx_sub properties *)

Lemma ctx_sub_refl : forall  {D:list (atom * sort)} {G}, ctx D G -> ctx_sub D G G.
Proof. induction D;
       move => G1 h; inversion h; subst.
       econstructor; auto. simpl_env. auto.
Qed.

Lemma ctx_sub_trans : forall  {G2} {D:list(atom * sort)} {G1 G3}, ctx_sub D G1 G2 -> ctx_sub D G2 G3 -> 
  ctx_sub D G1 G3.
Proof.
  move=> G2 D. move: G2.
  induction D; intros; inversion H0; inversion H; subst; auto.
  invert_equality.
  econstructor; auto.
  eapply IHD; eauto.
Qed.

Instance cst : forall {D:list (atom * sort)}, Transitive (ctx_sub D). 
intros. eauto using ctx_sub_trans.
Qed.

(* Interactions with association lists *)

Lemma dom_ctx_sub : forall  {D:list(atom * sort)} {G1 G2}, ctx_sub D G1 G2 -> dom G1 = dom G2.
Proof. move => D G1 G2 h. induction h; simpl; auto.
       all: rewrite IHh. 
       all: auto.
Qed.

Lemma uniq_ctx_sub : forall  {D:list(atom * sort)}{ G1 G2}, ctx_sub D G1 G2 -> uniq G1 <-> uniq G2.
Proof.
  move=> D G1 G2 h. induction h; split; auto;
  move => h1; inversion h1; subst.
  + erewrite dom_ctx_sub in H5; eauto.
  econstructor; eauto. 
  tauto.
  + erewrite <- dom_ctx_sub in H5; eauto.
  econstructor; eauto. 
  tauto.
Qed.

Lemma ctx_sub_app  {D1 D2 : list (atom  * sort)}{G1 G2 G3 G4} : 
  ctx_sub D1 G1 G2 -> ctx_sub D2 G3 G4 ->   uniq (D1 ++ D2) ->
  ctx_sub (D1 ++ D2) (G1 ++ G3) (G2 ++ G4).
Proof.
  induction 1. simpl. auto.
  all: intros h U; simpl_env; inversion U; subst.
  all: econstructor; eauto.
Qed.

(* decomposition *)

Lemma split_ctx_sub {D1:list (atom * sort)} : forall {G G1 D2 G4 G2},
  ctx D1 G -> ctx D1 G1
  -> ctx_sub (D1 ++ D2) (G ++ G4) (G1 ++ G2)
  -> ctx_sub D1 G G1 /\ ctx_sub D2 G4 G2.
Proof.
  induction D1; intros.
  inversion H; inversion H0.
  subst. simpl in *. split; auto.
  inversion H; inversion H0; inversion H1. subst.
  simpl_env in *.
  repeat invert_equality. 
  edestruct IHD1. 3: { eauto. } eclarify_ctx. eclarify_ctx.
  econstructor; eauto.
Qed.


Lemma ctx_sub_app_split_r  {D:list (atom * sort)} : forall {G G0 G3},
  ctx_sub D G (G0 ++ G3) -> 
  exists D1 D2 G1 G2, G = G1 ++ G2 /\ D = D1 ++ D2 /\ ctx_sub D1 G1 G0 /\ ctx_sub D2 G2 G3.
Proof.
  induction D.
  + intros G G0 G3 h. inversion h. exists nil. exists nil.
    exists nil. exists nil.
    repeat split; auto.
    destruct G0; destruct G3; simpl_env in *; inversion h.
    eauto.
    destruct G0; destruct G3; simpl_env in *; inversion h.
    eauto.
  + intros G G0 G3 h. 
    destruct G0; simpl_env in *; inversion h; subst.
    - clear h.
      specialize (IHD G1 nil G2 ltac:(eauto)).
      move: IHD => [D1 [D2 [G1' [G2' [h1 [h2 [h3 h4]]]]]]].
      inversion h3. subst. 
      exists nil.
      exists (x ~ a0 ++ D2).
      exists nil.
      exists (x ~ (q1,a0) ++ G2').
      simpl_env. split; auto.
    - clear h.
      specialize (IHD G1 G0 G3 ltac:(eauto)).
      move: IHD => [D1 [D2 [G1' [G2' [h1 [h2 [h3 h4]]]]]]].
      exists (x ~ a0 ++ D1).
      exists D2.
      exists (x ~ (q1, a0) ++ G1'). 
      exists G2'.
      subst.
      simpl_env. 
      repeat split; auto.
Qed.

Lemma three_ctx_sub {D:list(atom * sort)} : forall {G1 x q1 s G2 G},
    ctx_sub D (G1 ++ x ~ (q1, s) ++ G2) G -> 
    exists D1, exists D2, exists G1', exists G2', exists q2, D = D1 ++ x ~ s ++ D2 /\  G = G1' ++ x ~ (q2, s) ++ G2' /\
                        ctx_sub D1 G1 G1' /\ q_sub q1 q2 /\ ctx_sub D2 G2 G2'.
Proof.
  induction D; intros.
  + match goal with [ H : ctx_sub _ _ _ |- _ ] => inversion H end.
    destruct G1; simpl in *; discriminate.
  + destruct G1 as [|[y B] G1']. 
    ++ simpl in H. inversion H; subst.
       exists nil. eexists D. exists nil. exists G0. exists q2. simpl_env. auto.
    ++ inversion H. subst.
       simpl_env in *.
       specialize (IHD _ _ _ _ _ _ H7).
       move: IHD => [D1' [D2' [G1'' [G2'' [q2' [E1 [S1 [S2 [S3 S4]]]]]]]]].
       subst.
       exists (y ~ a0 ++ D1'). eexists.
       exists (y ~ (q2, a0) ++ G1''). eexists. eexists.
       simpl_env. 
       split; eauto.
Qed.


Ltac destruct_ctx_sub := 
    let D1 := fresh "D" in
    let D2 := fresh "D" in
    let G1' := fresh "G" in
    let G2' := fresh "G" in
    let E1  := fresh "E" in
    let S1  := fresh "S" in
    let S2  := fresh "S" in
    let S3  := fresh "S" in
    let q2  := fresh "q" in
    match goal with 
      | [H : ctx_sub ?D ?G (?G1 ++ ?G2) |- _ ] =>         
        apply ctx_sub_app_split_r in H;
        move: H => [D1 [D2 [G1' [G2' [E1 [S1 [S2 S3]]]]]]];
        subst G
     | [H : ctx_sub ?D (?G1 ++ ?x ~ (?q,?A) ++ ?G2) ?G |- _ ] =>         
        apply three_ctx_sub in H;
        move: H => [D1 [D2 [G1' [G2' [q2 [E1 [S1 [S2 [S3 S4]]]]]]]]];
        subst G 
     | [ H : ctx_sub ?D ?G3 ([(?x, ?s)] ++ ?G2) |- _ ] =>
       inversion H; subst; clear H
     | [ H : ctx_sub ?D ?G3 ([(?x, ?s)]) |- _ ] =>
       inversion H; subst; clear H
     | [ H : ctx_sub ?D ?G3 nil |- _ ] =>
       inversion H; subst; clear H
    end.
