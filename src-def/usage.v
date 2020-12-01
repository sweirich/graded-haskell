Require Import ssreflect.
Require Import Coq.Classes.EquivDec.
Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.

Require Export usage_sig.

(* ----------------------------------------------------------------- *)
(* Lemmas about the usage pre-order / semi-ring.                     *)
(* ----------------------------------------------------------------- *)

Open Scope usage_scope. 

(* --------------- Derived lemmas below here. -------------------- *)

Lemma usage_dec : forall x y, x =? y = true -> x = y.
Proof. intros. rewrite -> eqb_eq in H. auto. Qed.

(* --------------------------- *)

Lemma qplus_0_r : forall x, x + 0 = x.
Proof. 
  intros. rewrite qplus_comm. rewrite qplus_0_l. auto.
Qed.

(* --------------------------- *)

Lemma qplus_sub_r : forall u2 u u1, u1 <= u2 -> u1 + u <= u2 + u.
Proof.
  intros; eapply po_semiring1; auto.
Qed.  

Lemma qplus_sub_l : forall u2 u u1, u1 <= u2 -> u + u1 <= u + u2.
Proof.
  intros; repeat rewrite (qplus_comm u).
  apply po_semiring1. auto.
Qed.  

   
Lemma qplus_sub q1 q2 : 0 <= q2 -> q1 <= q1 + q2.
Proof.
  intros.
  move: (po_semiring1 _ _ q1 H) => h.
  rewrite qplus_0_l in h.
  rewrite qplus_comm.
  auto.
Qed.

Lemma qmul_sub2 q1 q2 : 1 <= q2 -> q1 <= q1 * q2.
Proof.
  move: (po_semiring3 1 q2 q1) => h.
  rewrite qmul_1_r in h.
  auto.
Qed.

Lemma qmul_sub_disposable : forall r q, 0 <= r -> 0 <= q * r.
Proof.
  intros.
  move: (po_semiring3 _ _ q H) => h.
  rewrite qmul_0_r in h.
  auto.
Qed. 

(* ----------------------------------------------------------------- *)
(* Tactics and Hints *)
(* ----------------------------------------------------------------- *)

(*
Add Ring usage_semi_ring : usage_semi_ring (decidable usage_dec).
Hint Resolve usage_semi_ring : usage.
*)

Hint Rewrite qplus_0_l qplus_0_r qmul_0_l qmul_0_r qmul_1_l qmul_1_r qplus_assoc qmul_assoc distr_l distr_r : usage.

Ltac ring_simpl := 
  repeat autorewrite with usage.

Tactic Notation "ring_simpl" "in" hyp(H) := 
  repeat autorewrite with usage in H.

Ltac ring_equal :=
  repeat (ring_simpl; f_equal).

Ltac asimpl := repeat (simpl; ring_simpl; simpl_env).

Tactic Notation "asimpl" "in" hyp(H) :=
  repeat (simpl in H; ring_simpl in H; simpl_env in H).


(* ---------------------------------------------------------------- *)

