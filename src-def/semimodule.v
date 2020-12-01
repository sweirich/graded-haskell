Require Import ssreflect.
Require Import Coq.Classes.EquivDec.
Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.

Require Import Qtt.tactics.
Require Import Qtt.usage.
Require Import Qtt.dctx.
Require Import Qtt.dctx_sub.

(* A Q-left semimodule is the definition of a carrier set M with commutative monoid structure (M,+,0) and left multiplication function. 

• for 𝑞1, 𝑞2 ∈ 𝑄 and 𝑚∈𝑀, we have (𝑞1 + 𝑞2) ⊙ 𝑚 = 𝑞1 ⊙ 𝑚 ⊕ 𝑞2 ⊙ 𝑚     [distrib2]
• for 𝑞 ∈ 𝑄 and 𝑚1,𝑚2 ∈ 𝑀, we have, 𝑞 ⊙ (𝑚1 ⊕ 𝑚2) = 𝑞 ⊙ 𝑚1 ⊕ 𝑞 ⊙ 𝑚2  [distrib]
 •for 𝑞1, 𝑞2 ∈𝑄 and 𝑚∈𝑀,we have (𝑞1·𝑞2) ⊙ 𝑚 = 𝑞1 ⊙ (𝑞2 ⊙ 𝑚)           [mul_assoc]
• for 𝑚 ∈ 𝑀, we have 1 ⊙ 𝑚 = 𝑚                                       [mul_id]
• for 𝑞 ∈ 𝑄 and 𝑚 ∈ 𝑀, we have 0 ⊙ 𝑚 = 𝑞 ⊙ 0 = 0.                     [mul_zero1, mul_zero2]

A left 𝑄-semimodule 𝑀 is said to be partially-ordered iff there exists a partial order ≤𝑀 on 𝑀 such that the following properties hold.
• for 𝑚1,𝑚2, 𝑚 ∈ 𝑀, if 𝑚1 ≤𝑀 𝑚2, then 𝑚 ⊕ 𝑚1 ≤𝑀 𝑚 ⊕ 𝑚2            [ctx_sub_ctx_plus]
• for 𝑞 ∈ 𝑄 and 𝑚1,𝑚2 ∈ 𝑀, if 𝑚1 ≤𝑀 𝑚2, then 𝑞 ⊙ 𝑚1 ≤𝑀 𝑞 ⊙ 𝑚2       [po_semiring_context]
• for 𝑞1,𝑞2 ∈𝑀 and 𝑚∈𝑀, if 𝑞1 ≤𝑞2, then 𝑞1 ⊙ 𝑚 ≤ 𝑀  𝑞2 ⊙ 𝑚.           [ctx_sub_ctx_mul]
*)

(* Here we show that contexts form a module; uses ctx_plus, ctx_mul, and ctx_sub. *)

(* We reorient some of these properties so that we can add them to rewr_list hint database. 
   That way they will be automatically applied by the [simpl_env] tactic.  *)


Section CtxMod.

Variables A:Type.

(* First, ctx_plus with 0=(ctx_mul 0 G) is a commutative monoid. *)

Lemma ctx_plus_0_l : forall (G:list(atom*(usage*A))),
  G = ctx_plus (ctx_mul 0 G) G.
Proof.
  induction G; simpl. auto.
  destruct a as [x [q1 ?]].
  simpl.
  ring_equal.
  auto.
Qed. 

Lemma ctx_plus_0_r : forall (G:list(atom*(usage*A))),
  G = ctx_plus G (ctx_mul 0 G).
Proof.
  induction G; simpl. auto.
  destruct a as [x [q1 ?]].
  simpl.
  ring_equal.
  auto.
Qed. 

(* if we add a pre-condition, we can generalize this identity. *)

Lemma ctx_ctx_plus_0_l : forall {D:list(atom*A)} {G1 G2},
  ctx D G1 -> 
  ctx D G2 ->
  ctx_plus (ctx_mul 0 G1) G2 = G2.
Proof.
  induction D; intros; destruct_ctx; simpl. auto.
  ring_equal.
  auto.
Qed. 

Lemma ctx_ctx_plus_0_r : forall {D:list(atom*A)} {G1 G2},
  ctx D G1 -> 
  ctx D G2 ->
  ctx_plus G2 (ctx_mul 0 G1) = G2.
Proof.
  induction D; intros; destruct_ctx; simpl. auto.
  ring_equal.
  auto.
Qed. 

(* Associativity also has a precondition. *)

Lemma ctx_plus_assoc : forall D (G1:list(atom*(usage*A))) G2 G3, 
    ctx D G1 -> 
    ctx D G2 -> 
    ctx D G3 -> 
    ctx_plus (ctx_plus G1 G2) G3 = ctx_plus G1 (ctx_plus G2 G3).
Proof.
  induction D; intros; invert_ctx; simpl; auto.
  f_equal. f_equal. f_equal. ring_equal. 
  eauto.
Qed.


Lemma ctx_plus_comm : 
  forall D (G1:list(atom*(usage*A))) G2, ctx D G1 -> ctx D G2 -> ctx_plus G1 G2 = ctx_plus G2 G1.
Proof. 
  induction D; intros; invert_ctx. auto.
  simpl.
  f_equal. f_equal. rewrite qplus_comm. auto.
  rewrite IHD; auto.
Qed.



(* Next, the explicit module laws *)

Lemma ctx_distrib2 q1 q2 (G:list(atom*(usage*A))) : forall (D:list(atom*A)) G1 G2, ctx D G1 -> ctx D G2 -> 
  ctx_plus (ctx_mul q1 G) (ctx_mul q2 G) = ctx_mul (q1 + q2) G.
Proof. 
  induction G. intros. simpl. auto.
  intros. destruct a as [x [? ?]].
  simpl.
  rewrite distr_l.
  f_equal.
  eauto.
Qed.


Lemma ctx_distrib1 r D (G1:list(atom*(usage*A))) : ctx D G1 -> forall G G2, ctx D G2 ->
  G = ctx_plus G1 G2 -> (ctx_mul r G) = ctx_plus (ctx_mul r G1) (ctx_mul r G2).
Proof. 
  induction 1; intros; invert_ctx. auto.
  simpl.
  rewrite distr_r.
  f_equal.
  auto.
Qed.

Lemma ctx_distrib {r D}{G1:list(atom*(usage*A))} G2 : ctx D G1 -> ctx D G2 ->
  ctx_mul r (ctx_plus G1 G2) = ctx_plus (ctx_mul r G1) (ctx_mul r G2).
Proof. 
  intros.
  eapply ctx_distrib1; eauto.
Qed.


Lemma ctx_mul_assoc q1 q2 {G:list(atom*(usage*A))} : ctx_mul q1 (ctx_mul q2 G) = ctx_mul (q1 * q2) G.
Proof.
   induction G; simpl; try done.
   destruct a as [x [? ?]].
   simpl.
   rewrite IHG.
   rewrite qmul_assoc.
   auto.
Qed.

Lemma ctx_mul_id : forall {G:list(atom*(usage*A))}, ctx_mul 1 G = G.
Proof. 
  induction G. auto.   
  destruct a as [x [? ?]].
  simpl. rewrite IHG.
  rewrite qmul_1_l. auto.
Qed.

(* The identities for multiplying by zero are a bit tricky. ctx_mul 0 G is defined to be zero, for any G. 
   So the identities listed above are a bit trivial.
*)

(* This lemma says that all zeros are the same *)
Lemma same_ctx : forall {D}{G1:list(atom*(usage*A))}, ctx D G1 -> forall G2, ctx D G2 -> ctx_mul 0 G1 = ctx_mul 0 G2.
Proof.
  induction 1; intros; invert_ctx; simpl_env. auto.
  simpl. erewrite IHctx.
  repeat rewrite qmul_0_l.
  f_equal.
  auto.
Qed.

(* This is another variant of the same lemma *)
Lemma ctx_mul_0_eq : forall {G1 G2:list(atom*(usage*A))}, ctx_mul 0 G1 = G2 -> ctx_mul 0 G2 = G2. 
Proof.
  intros G1. induction G1.
  - intros. destruct G2; inversion H. auto.
  - intros. simpl in H. destruct a. destruct p. simpl in H.
    destruct G2; inversion H.
    destruct p. destruct p. inversion H1. subst. clear H1.
    asimpl. rewrite ctx_mul_assoc. asimpl. auto.
Qed.

(* --------------- Partially-ordered semimodule ------------------- *)


Lemma po_semiring_context {q}{D:list(atom*A)}{G1 G2} : 
     ctx_sub D G1 G2 
   -> ctx_sub D (ctx_mul q G1) (ctx_mul q G2). 
Proof.
  induction 1. simpl. auto.
  simpl. econstructor; auto.
  eapply po_semiring3. auto.
Qed. 



Lemma ctx_sub_ctx_mul: forall {D} {G:list(atom*(usage*A))} {q3 q0}, q3 <= q0 -> ctx D G -> ctx_sub D (ctx_mul q3 G) (ctx_mul q0 G).
Proof. induction 2. simpl. auto.
       econstructor; auto. apply po_semiring2. auto. 
Qed.



Lemma ctx_sub_ctx_plus_aux: 
  forall {D}{G3':list(atom*(usage*A))} {G3}, 
    ctx_sub D G3' G3 -> forall G, ctx D G ->
    ctx_sub D (ctx_plus G3' G) (ctx_plus G3 G).
Proof.
  induction 1; intros; invert_ctx; simpl; auto.
  econstructor; eauto.
  eapply qplus_sub_r; auto.
Qed. 

Lemma ctx_sub_ctx_plus: forall {D:list (atom*A)}{G1 G1' G2 G2'}, 
    ctx_sub D G1 G1' -> ctx_sub D G2 G2' ->
    ctx_sub D (ctx_plus G1 G2) (ctx_plus G1' G2').
Proof.
  intros.
  transitivity (ctx_plus G1 G2').
  rewrite (@ctx_plus_comm D G1 G2); try eassumption.
  eapply ctx_sub_ctx1; eauto.
  eapply ctx_sub_ctx1; eauto.
  rewrite (@ctx_plus_comm D G1 G2'); try eassumption.
  eapply ctx_sub_ctx1; eauto.
  eapply ctx_sub_ctx2; eauto.
  eapply ctx_sub_ctx_plus_aux; eauto.
  eapply ctx_sub_ctx1; eauto.
  eapply ctx_sub_ctx_plus_aux; eauto.
  eapply ctx_sub_ctx2; eauto.
Qed. 


(* --------------- Derived properties ------------------- *)


Lemma ctx_plus_sub: forall {D1} {G1 G2' G2:list(atom*(usage*A))}, ctx D1 G1 -> 
                               G2' = ctx_mul 0 G2' ->
                               ctx_sub D1 G2' G2 -> ctx_sub D1 G1 (ctx_plus G1 G2).
Proof. 
induction D1; intros; invert_ctx; simpl; auto.
inversion H1. auto.
simpl_env in *. inversion H1. subst. simpl. 
unfold ctx_mul in H0. simpl_env in H0. inversion H0. 
econstructor. auto. eapply qplus_sub. rewrite H2 in H5. ring_simpl in H5. auto.
eauto. auto.
Qed. 



Lemma ctx_plus_swap: forall {D:list(atom*A)} a,
    ctx D a -> forall b c d, ctx D b ->
    ctx D c -> ctx D d ->
    ctx_plus (ctx_plus a b) (ctx_plus c d) = 
    ctx_plus (ctx_plus a c) (ctx_plus b d).
Proof.
  induction 1; intros;
  simpl in *.
  - inversion H. inversion H0. inversion H1. auto.
  - inversion H1. inversion H2. inversion H3. subst. 
    asimpl.
    rewrite IHctx; try eclarify_ctx.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    rewrite <- qplus_assoc.
    rewrite <- qplus_assoc.
    f_equal.
    rewrite qplus_comm.
    auto.
Qed.



Lemma ctx_plus_ctx_mul_0 : forall (G:list(atom*(usage*A))) G1 G2, G = ctx_plus (ctx_mul 0 G1) (ctx_mul 0 G2) -> 
                          G = ctx_mul 0 G.
Proof.
  induction G; intros; simpl; auto.
  destruct a as [x [q ?]]. 
  destruct G1 as [|[y [q1' ?]]];
  destruct G2 as [|[z [q1 ?]]]; simpl in H; try inversion H. subst. clear H.
  simpl. repeat rewrite qmul_0_l. repeat rewrite qplus_0_l.
  repeat f_equal.
  eauto. 
Qed.  


End CtxMod.


(* by adding these lemmas to the rewr_list hint database, it will be automatically 
   applied by the [simpl_env] tactic.  *)

Hint Rewrite ctx_mul_id : rewr_list.
Hint Rewrite ctx_mul_assoc : rewr_list.
Hint Rewrite ctx_distrib2 : rewr_list.

Hint Rewrite ctx_ctx_plus_0_l ctx_ctx_plus_0_r : rewr_list.
