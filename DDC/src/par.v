Require Import Omega.
Require Export Qual.geq.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

(* ------------------------------------------------- *)


(* ValueTypes keep the same form under reduction. *)

Ltac par_preserves_head := 
  induction 1; intros; subst; try discriminate; try inversion H; try reflexivity; try eauto;
  try match goal with [ H :(_ _) = (_ _) |- _ ] => inversion H; subst; eauto end.


Lemma Par_Type_inv : forall S A psi B s, Par S psi A B -> A = a_Type s -> B = a_Type s.
Proof. par_preserves_head. Qed.

Lemma Par_TyUnit_inv : forall S A psi B, Par S psi A B -> A = a_TyUnit -> B = a_TyUnit.
Proof. par_preserves_head. Qed.

Lemma Par_Pi_inv : forall S D rho A B, Par S D A B -> forall A1 A2,
      A = a_Pi rho A1 A2 -> exists B1 B2, B = (a_Pi rho B1 B2).
Proof. par_preserves_head. Qed.

Lemma Par_WSigma_inv : forall S D rho A B, Par S D A B -> forall A1 A2,
      A = a_WSigma rho A1 A2 -> exists B1 B2, B = (a_WSigma rho B1 B2).
Proof. par_preserves_head. Qed.

Lemma Par_SSigma_inv : forall S D rho A B, Par S D A B -> forall A1 A2,
      A = a_SSigma rho A1 A2 -> exists B1 B2, B = (a_SSigma rho B1 B2).
Proof. par_preserves_head. Qed.

Lemma Par_Sum_inv : forall S D A B, Par S D A B -> forall A1 A2,
      A = a_Sum A1 A2 -> exists B1 B2, B = (a_Sum B1 B2).
Proof. par_preserves_head. Qed.


(* ------------------------------------------------- *)

Lemma CPar_Par_Grade : (forall P psi phi a b, CPar P psi phi a b -> CGrade P psi phi a /\ CGrade P psi phi b) /\ 
                       (forall P psi a b, Par P psi a b -> Grade P psi a /\ Grade P psi b).
Proof. 
  apply CPar_Par_mutual.
  all: split; split_hyp; eauto.
  all: try solve [invert_Grade; subst; auto].
  all: try solve [fresh_apply_Grade x; auto; repeat spec x; split_hyp; eauto].
  - (* Beta *)
    invert_Grade; subst; pick fresh y; repeat spec y. invert_CGrade b'. eapply Grade_open; eauto. eapply Grade_open_irrel; eauto.
  - (* Par_WPairBeta *)
    invert_Grade; subst; pick fresh y; repeat spec y; split_hyp; eauto.
    eapply G_App; eauto using leq_Bot.
    invert_CGrade a1'.
        eapply Grade_open; eauto.
         eapply Grade_open_irrel; eauto.
  - (* Proj1 *)
    invert_Grade; subst. invert_CGrade a1'. auto. done.
Qed.

Lemma Par_Grade : forall P psi a b, Par P psi a b -> Grade P psi a /\ Grade P psi b.
Proof. apply CPar_Par_Grade. Qed.

Lemma Par_Grade1 : forall P psi a b, Par P psi a b -> Grade P psi a.
Proof.  eapply Par_Grade. Qed.

Lemma Par_Grade2 : forall P psi a b, Par P psi a b -> Grade P psi b.
Proof.  eapply Par_Grade. Qed.

Lemma MultiPar_Grade : forall P psi a b, MultiPar P psi a b -> Grade P psi a /\ Grade P psi b.
induction 1; split; split_hyp; eauto using GEq_Grade1, GEq_Grade2, Par_Grade1.
Qed.

Lemma MultiPar_Grade1 : forall P psi a b, MultiPar P psi a b -> Grade P psi a.
Proof.  eapply MultiPar_Grade. Qed.

Lemma MultiPar_Grade2 : forall P psi a b, MultiPar P psi a b -> Grade P psi b.
Proof.  eapply MultiPar_Grade. Qed.



Lemma MultiPar_refl : forall S D a, Grade S D a -> MultiPar S D a a.
Proof.
  intros. eapply MP_Refl. auto.
Qed.

Lemma MultiPar_trans : forall S D a b c, MultiPar S D a b -> MultiPar S D b c -> MultiPar S D a c.
Proof.
  intros.
  induction H. auto.
  eauto.
Qed.


Lemma MultiPar_subst3_CMultiPar : 
    forall P1 a a' x phi psi, MultiPar ([(x,phi)] ++ P1) psi a a' ->    
    forall b b', CMultiPar P1 psi phi b b' ->
    MultiPar P1 psi (subst b x a) (subst b' x a').
Proof.
  intros P1 a a' x phi psi MP.
  intros b b' CMP.
  eapply MultiPar_trans with (b := subst b' x a).
  + inversion CMP; subst.
    ++ induction H0. 
       eapply MP_Refl. 
       eapply Grade_substitution_same with (P2 := nil); eauto using MultiPar_Grade1.
       eapply MP_Step with (b:= (subst b x a)).
       eapply Par_subst3; eauto. 
       eapply Par_Refl; eauto using MultiPar_Grade1.
       eapply IHMultiPar; eauto.
    ++ eapply MP_Step with (b := subst b' x a).
       eapply Par_subst3; eauto.
       eapply Par_Refl; eauto using MultiPar_Grade1.
       eapply MP_Refl.
       eapply Grade_substitution_irrel with (P2 := nil); eauto using MultiPar_Grade1.
  + have Gb' : CGrade P1 psi phi b'.
    { inversion CMP; subst; eauto using MultiPar_Grade2. }
    clear b CMP.
    move: b' Gb'.
    dependent induction MP; intros.
    ++ eapply MP_Refl.
       eapply Grade_substitution_CGrade with (P2 := nil); eauto.
    ++ eapply MP_Step with (b := subst b' x b).
       eapply Par_substitution_CGrade with (P2 := nil); eauto.
       eapply IHMP; eauto.
Qed.       

Lemma MultiPar_subst3 : 
    forall P1 a a' x phi psi, MultiPar ([(x,phi)] ++ P1) psi a a' ->    
    forall b b', MultiPar P1 psi b b' ->
    MultiPar P1 psi (subst b x a) (subst b' x a').
Proof.
  intros. eapply MultiPar_subst3_CMultiPar; eauto.
  destruct (q_leb phi psi) eqn: LE.
  eauto.
  eapply CMP_Nleq; eauto using MultiPar_lc1, MultiPar_uniq.
  eapply MultiPar_lc2. eauto. rewrite LE. done.
Qed.

Lemma MultiPar_weakening_middle :
  forall E G a psi b, MultiPar (E ++ G) psi a b ->
  forall F, uniq (E ++ F ++ G) -> MultiPar (E ++ F ++ G) psi a b.
Proof.
  intros E G a psi b H.
  dependent induction H; intros. eapply MP_Refl; eauto using Grade_weakening_middle.
  eapply MP_Step. 
  eapply Par_weakening_middle; eauto.
  eapply IHMultiPar; eauto.
Qed.


Lemma MultiPar_renaming : forall y x psi0 P psi b1 b2, 
    x `notin` dom P \u fv b1 \u fv b2 -> 
    y `notin` dom P \u fv b1 \u fv b2 \u {{x}} -> 
    MultiPar ([(y, psi0)] ++ P) psi (open b1 (a_Var_f y)) (open b2 (a_Var_f y)) -> 
    MultiPar ([(x, psi0)] ++ P) psi (open b1 (a_Var_f x)) (open b2 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_intro y b1); auto.
  rewrite (subst_intro y b2); auto.
  move: (MultiPar_uniq H1) => u. 
  eapply MultiPar_subst3_CMultiPar.
  eapply MultiPar_weakening_middle; eauto.
  destruct (q_leb psi0 psi) eqn:LE.
  eapply CMP_Leq; eauto. eapply MP_Refl. eapply G_Var; eauto. solve_uniq.
  eapply CMP_Nleq; eauto with lc. rewrite LE. done. solve_uniq.
Qed.


(* ------------------------------------------------- *)

Lemma Step_Par : forall a b, Step a b -> forall W psi, Grade W psi a -> Par W psi a b.
Proof.
  induction 1; intros.
  all: try invert_Grade; subst. 
  all: try specialize (IHStep _ _ ltac:(eassumption)).
  all: eauto using GEq_refl.
  all: invert_CGrade b; eauto.
Qed.


(*  
      a  =  a'
      |    .|.
      b .=. b'

 *)


Local Ltac  Par_respects_ih b':= 
  match goal with [H3 : forall a', GEq ([(?x, _)] ++ _) ?psi (open ?B1 (a_Var_f ?x)) a' -> _
                   |- _ ] =>  move: (H3 _ ltac:(eassumption)) => [b' ?]; split_hyp end.  


Lemma CPar_Par_respects_GEq : 
  (forall W psi phi a b, CPar W psi phi a b -> forall a', CEq W psi phi a a' -> exists b', CPar W psi phi a' b' /\ CEq W psi phi b b') /\
  (forall W psi a b, Par W psi a b -> forall a', GEq W psi a a' -> exists b', Par W psi a' b' /\ GEq W psi b b').
Proof.
  apply CPar_Par_mutual.
  all: intros; eauto. 
  (* refl *)
  exists a'. split; eauto 4 using GEq_refl, GEq_Grade2. 
  all: try (invert_GEq ; subst).
  all: try (move: (H _ ltac:(eauto 2)) => [a1' [P1' GE1']]; clear H).
  all: let b2' := fresh "b2'" in try (move: (H0 _ ltac:(eauto 1)) => [b2' [P2' GE2']]; clear H0).
  all: try (move: (H1 _ ltac:(eauto 1)) => [a3' [P3' GE3']]; clear H1). 
  all: let b4' := fresh "b4'" in try (move: (IHPar3 _ ltac:(eauto 1)) => [b4' [P4' GE4']]; clear IHPar3).

  all: try done.
  all: try solve [ eexists;  split; eauto 3 ].
  - (* Pi *)
    pick fresh x; repeat spec x.
    Par_respects_ih b'.
    exists (a_Pi psi1 a1' (close x b')).
    split.
    exists_apply_Par x.
    exists_apply_GEq x.
  - (* App Rel *)
    inversion GE1'; subst; clear GE1'.
    pick fresh y; repeat spec y.
    exists (open b0 b2').
    split.
    eapply Par_AppBeta; eauto.
    eapply GEq_open; eauto.
  - (* Abs cases *)    
    pick fresh x. repeat spec x.
    Par_respects_ih b'.
    exists (a_Abs psi0 b2' (close x b')).
    split.
    exists_apply_Par x.
    exists_apply_GEq x.
  - (* WSigma *)
    pick fresh x; repeat spec x.
    Par_respects_ih b'.
    exists (a_WSigma psi1 a1' (close x b')).
    split.
    exists_apply_Par x.
    exists_apply_GEq x.
  - (* LetPair *)
    move: (Par_Grade p) => [Ga GWP].  
    edestruct H as [a3 [Pa GE]]; eauto. invert_GEq. subst.
    pick fresh x.  repeat spec x.
    Par_respects_ih a4'.
    exists (a_App (open (close x a4') a4) q_Bot b4).
    split.
    exists_apply_Par x.
    eapply GEq_App.
    eapply GEq_open; eauto. rewrite fv_close. auto.
    rewrite open_close. auto.
    eapply CEq_Leq; eauto using leq_Bot. 
  - (* LetPair Cong *)
    pick fresh x. repeat spec x.
    Par_respects_ih a4'.
    exists (a_LetPair psi0 a1' (close x a4')).
    split.
    exists_apply_Par x. 
    exists_apply_GEq x. 
  - (* SSigma *)
    pick fresh x; repeat spec x.
    Par_respects_ih b'.
    exists (a_SSigma psi1 a1' (close x b')).
    split.
    exists_apply_Par x.
    exists_apply_GEq x.
    
  - (* proj1 *)
    edestruct H as [a4 [Pa E]]; eauto.
    invert_GEq. subst.
    exists a5. split; eauto. 
    inversion H8. subst. auto. done.
  - (* proj2 *)
    edestruct H as [a4 [Pa E]]; eauto.
    invert_GEq. subst.
    exists b2. split; eauto.
  - (* inj1 *) edestruct H as [a4 [Pa E]]; eauto.
  - (* case *)
    inversion GE1'. subst. clear GE1'.
    exists (a_App b2'1 psi0 a1'0).
    split; eauto.
  - (* case *)
    inversion GE1'. subst. clear GE1'.
    exists (a_App a3' psi0 a2').
    split; eauto.
  - (* subst *)
    edestruct H as [a4 [Pa E]]; eauto. 
    inversion H0; subst. auto. done. 
  - inversion H; subst. done.
    eauto.
Qed.  

Lemma Par_respects_GEq : forall W a psi b, Par W psi a b -> forall a', GEq W psi a a' -> exists b', Par W psi a' b' /\ GEq W psi b b'.
Proof. intros. move: CPar_Par_respects_GEq => [_ h]. eauto. Qed.

(* ------------------------------------------------- *)


Lemma open2 :
  forall x b b' W a a' phi psi,
    x `notin` fv a' \u fv a \u dom W ->
    Par ([(x,phi)] ++ W) psi (open a (a_Var_f x)) (open a' (a_Var_f x)) ->
    CPar W psi phi b b' ->
    Par W psi (open a b) (open a' b').
Proof.
  intros x b b'. intros.
  rewrite (subst_intro x); auto.
  rewrite [(_ _ b')] (subst_intro x); auto.
  replace W with (nil ++ W); auto.
  eapply Par_subst3; eauto.
Qed.


Lemma Par_open_preservation: forall G B1 psi B2 x, 
    Par G psi (open B1 (a_Var_f x)) B2 -> 
    exists B', B2 = open B' (a_Var_f x) /\ 
          Par G psi (open B1 (a_Var_f x)) (open B' (a_Var_f x)).
Proof.
  intros G B1 psi B2 x H.
  exists (close x B2).
  have:open (close x B2) (a_Var_f x) = B2 by apply open_close.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.


