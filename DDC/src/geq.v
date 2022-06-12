Require Export Qual.grade.

Set Implicit Arguments.

(* Notes:

   Consider P |- psi a ~~ b

   We need to have P |- psi a (GEq_Grade) so that we do lifting/equality
   substitution. We need to know which variables are relevant (those in P with
   grades <= psi) and which ones are not.

   Reflexivity requires P |- psi a 

   Lifting:
  
           P, x:psi |- phi b
           P |- phi psi a1 ~ a2
           P |- phi b {a1/x} ~~ b {a2/x}
*)


(* relationship to grade *)


Lemma CEq_GEq_Grade : 
  (forall P phi phi0 a b,
  CEq P phi phi0 a b -> CGrade P phi phi0 a /\ CGrade P phi phi0 b) /\
  (forall P phi a b,
  GEq P phi a b -> Grade P phi a /\ Grade P phi b).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; split_hyp; split; eauto using leq_join_r.
  all: try solve [fresh_apply_Grade x; eauto;
    repeat spec x; split_hyp; eauto].
Qed.

Lemma GEq_Grade1 :
  (forall P phi a b,
  GEq P phi a b -> Grade P phi a).
Proof. apply CEq_GEq_Grade. Qed.
Lemma GEq_Grade2 :
  (forall P phi a b,
  GEq P phi a b -> Grade P phi b).
Proof. apply CEq_GEq_Grade. Qed.

(* ------------------------------ context stuff ----------------------- *)


(* Graded/Guarded equality is an equivalence/congruence relation, closed under substitution and implies consistency. *)

Lemma CEq_GEq_refl : (forall P phi psi a, CGrade P phi psi a -> CEq P phi psi a a) /\ 
                     (forall P phi a, Grade P phi a -> GEq P phi a a).
Proof. 
  apply CGrade_Grade_mutual.
  all: intros; eauto.
Qed.

Lemma GEq_refl :  (forall P phi a, Grade P phi a -> GEq P phi a a).
  apply CEq_GEq_refl; auto.
Qed.

Lemma CEq_refl : forall P phi a psi, CGrade P phi psi a -> CEq P phi psi a a.
Proof.
  destruct CEq_GEq_refl; auto.
Qed.

Lemma CEq_GEq_sym : 
  (forall P phi phi0 a b,
  CEq P phi phi0 a b -> CEq P phi phi0 b a) /\
  (forall P phi a b,
  GEq P phi a b -> GEq P phi b a).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; eauto. 
Qed.

Lemma GEq_symmetry :   (forall P phi a b,
  GEq P phi a b -> GEq P phi b a).
Proof. apply CEq_GEq_sym. Qed.
  
Lemma CEq_GEq_trans : 
  (forall P  phi phi0 a b,
  CEq P phi phi0 a b -> forall c, CEq P phi phi0 b c  -> CEq P phi phi0 a c) /\
  (forall P phi a b,
  GEq P phi a b -> forall c, GEq P phi b c -> GEq P phi a c).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; subst; eauto.
  all: try match goal with 
    | [ H: GEq ?P ?ps (_ _ ) ?c |- _ ] => inversion H; subst; clear H end.
  all: eauto.

  all: try (fresh_apply_GEq x; eauto; repeat spec x).
  - (* leq *)
    inversion H0. subst. eauto. done.
  - (* nleq *)
    inversion H; subst. done.
    eapply CEq_Nleq; eauto. 
Qed.


Lemma GEq_trans : forall P phi a b c, GEq P phi a b -> GEq P phi b c -> GEq P phi a c.
Proof. 
  intros.
  destruct CEq_GEq_trans.
  eapply H2; eauto. 
Qed.

(* ------------------------------------------------------- *)

(*
     b1  ->  b2
  phi =     phi .= 
     b1' .-> b2'

*)

Lemma CEq_GEq_respects_Step : 
  (forall P phi phi0 b1 b1',
  CEq P phi phi0 b1 b1' ->  forall b2, Step b1 b2 -> 
       exists b2', (phi0 <= phi -> Step b1' b2') /\ CEq P phi phi0 b2 b2') /\
  (forall P phi b1 b1',
  GEq P phi b1 b1' -> forall b2, Step b1 b2 ->
       exists b2', Step b1' b2' /\ GEq P phi b2 b2').
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; subst; eauto. 
  all: match goal with [ H : Step _ _ |- _ ] => inversion H; subst end.
  all: try
    let b2' := fresh in
    let ss' := fresh in 
    let GE' := fresh in
    match goal with [ H : forall b3, Step ?b1 b3 -> _ , H2 : Step ?b1 ?a' |- _ ] => 
                  destruct (H _ H2) as [b2' [ss' GE']] ; clear H end.
  all: split_hyp. 
  all: try solve [
             eexists; split; 
             econstructor;
             eauto 3 using CEq_refl, GEq_lc2, CEq_lc2, CEq_uniq].
  (* all: try solve [
             inversion g; subst;
             eexists; split; eauto using GEq_lc2, CEq_lc2]. *)
  all: try solve [
    eexists; split; try (intro h; eauto; done);
    eapply CEq_Leq; eauto].
  all: try solve [
    eexists; split; try (intro h; done);
    eapply CEq_Nleq; eauto 3 using Step_lc2] .
 
  - (* beta *)
    inversion g. subst. 
    pick fresh x. spec x.
    exists (open_tm_wrt_tm b0 a2). split.
    econstructor; eauto using GEq_lc2; eauto using CEq_lc2.
    eapply GEq_open; eauto.
  - (* LetPair beta *)
    inversion g. subst.
    pick fresh x. spec x.
    exists (a_App (open_tm_wrt_tm b2 a4) q_Bot b3). split.
    econstructor; eauto using GEq_lc2; eauto using CEq_lc2.
    econstructor; eauto.
    eapply GEq_open; eauto.
    eapply CEq_Leq; eauto using leq_Bot.
  - (* Proj1 beta *)
    inversion g. subst.
    exists a0. split.
    econstructor; eauto using GEq_lc2, CEq_lc2.
    inversion H9; subst; auto. done.
  - (* Proj2 beta *)
    inversion g; subst.
    eexists b0. split; auto;
    econstructor; eauto using GEq_lc2, CEq_lc2.
  - (* Case beta *)
    inversion g; subst.
    eexists (a_App b1' psi0 a1'). split; auto.
    eapply S_Case1Beta; eauto using GEq_lc2, CEq_lc2.
  - inversion g; subst.
    eexists (a_App b2' psi0 a2'). split; auto.
    eapply S_Case2Beta; eauto using GEq_lc2, CEq_lc2.
Qed.

