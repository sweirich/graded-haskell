Require Export Qual.tactics.
Require Export Qual.typing.
Require Export Qual.consist.

Set Implicit Arguments.
Open Scope grade_scope.

(* Erasure operation: convert any parts of the term marked higher than psi to TmUnit.   *)

Fixpoint erasure (phi : grade) (a:tm)  : tm := 
  match a with 
  | a_TyUnit => a_TyUnit 
  | a_TmUnit => a_TmUnit 
  | (a_Pi psi A B) => a_Pi psi (erasure phi A) (erasure phi B)
  | (a_Abs psi A a) => 
      if q_leb q_Top phi then 
        a_Abs psi (erasure phi A) (erasure phi a)
      else 
        a_Abs psi a_TmUnit (erasure phi a)
  | (a_App a psi b) => 
      if q_leb psi phi then 
        a_App (erasure phi a) psi (erasure phi b)
      else 
        a_App (erasure phi a) psi a_TmUnit
  | (a_Type s) => a_Type s
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_Sum A1 A2) => a_Sum (erasure phi A1) (erasure phi A2)
  | (a_Inj1 a) => a_Inj1 (erasure phi a)
  | (a_Inj2 a) => a_Inj2 (erasure phi a)
  | (a_Case psi a b1 b2) => a_Case psi (erasure phi a) (erasure phi b1) (erasure phi b2)
  | (a_WSigma psi A B) => a_WSigma psi (erasure phi A) (erasure phi B)
  | (a_WPair a psi b) => 
      if q_leb psi phi then 
        a_WPair (erasure phi a) psi (erasure phi b)
      else 
        a_WPair a_TmUnit psi (erasure phi b)
  | (a_LetPair psi a b) => a_LetPair psi (erasure phi a) (erasure phi b)
  | (a_SSigma psi A B) => a_SSigma psi (erasure phi A) (erasure phi B)
  | (a_SPair a psi b) => 
      if q_leb psi phi then 
        a_SPair (erasure phi a) psi (erasure phi b)
      else 
        a_SPair a_TmUnit psi (erasure phi b)
  | (a_Proj1 psi a) => a_Proj1 psi (erasure phi a)
  | (a_Proj2 psi a) => a_Proj2 psi (erasure phi a)
end.


(* Erasure and locally nameless representation infrastructure lemmas *)

Lemma erasure_open_rec : forall a b psi k, 
  (erasure psi (open_rec k a b)) = open_rec k (erasure psi a) (erasure psi b).
Proof. 
  intros a b psi. induction b; intros; cbn; auto.
  all: try rewrite IHb1.
  all: try rewrite IHb2.
  all: try rewrite IHb3.
  all: try rewrite IHb.
  all: auto.
  all: try (destruct (q_leb psi0 psi) eqn:LP; simpl).
  all: try (destruct (q_leb q_Top psi) eqn:LT; simpl).
  all: auto.
  all: try (destruct (lt_eq_lt_dec n k) eqn:LE; simpl; auto).
  all: try (destruct s; simpl; auto).
Qed.

Lemma erasure_open : forall a b psi, 
  erasure psi (open a b) = open (erasure psi a) (erasure psi b).
Proof. 
  intros. unfold open. rewrite erasure_open_rec. auto.
Qed.

Section lc.

#[local] Transparent Syntax_tm.

Lemma erasure_lc : forall psi a, lc a -> lc (erasure psi a).
Proof. 
  intros. induction H; simpl; eauto with lc.
  all: try solve [destruct (q_leb psi0 psi) eqn:LE; eauto with lc].
  all: destruct (q_leb q_Top psi) eqn:LT.
  all: try solve [econstructor; eauto with lc;
    match goal with [H1 : forall x : tmvar, lc (erasure _ _) |- _ ] => 
    intro x; specialize (H1 x);
    rewrite erasure_open in H1; simpl in H1; auto end].  
Qed.
End lc.

#[local] Hint Resolve erasure_lc : lc.

#[global] Opaque Syntax_tm.

Lemma canonical_body : forall L B1 B2 psi, 
  (forall x : atom,
       x `notin` L ->
       erasure psi (open B1 (a_Var_f x)) =
       erasure psi (open B2 (a_Var_f x))) ->
  erasure psi B1 = erasure psi B2.
Proof.
  intros.
  pick fresh x for (fv (erasure psi B1) \u fv (erasure psi B2) \u L). repeat spec x.
  apply (open_inj _ _ x);  eauto.
  rewrite erasure_open in H0.
  rewrite erasure_open in H0.
  simpl in H0. auto.
Qed.

(* Substitution lemma *)

(* Unobservable variables do not appear in erased terms. *)

Lemma CGrade_Grade_fv_erasure : (forall P psi psi0 b,
      CGrade P psi psi0 b -> forall P1 P2 x phi, 
        P = P2 ++ [(x,phi)] ++ P1 
        -> not (phi <= psi)
        -> psi0 <= psi
        -> x `notin` fv (erasure psi b)) /\
      (forall P psi b, 
          Grade P psi b -> forall P1 P2 x phi, 
            P = P2 ++ [(x,phi)] ++ P1 
            -> not (phi <= psi)
            -> x `notin` fv (erasure psi b)).
Proof.
  apply CGrade_Grade_mutual. 
  all: intros; subst; unfold erasure; fold erasure; simp_syntax; auto.
  all: try solve [destruct (x == x0) eqn:E; subst; auto;
    apply binds_mid_eq in b; subst; auto; done].  
  all: try (eapply notin_union).
  all: eauto.
  all: try (destruct (q_leb psi0 psi) eqn:LE; try rewrite LE).
  all: eauto.
  all: try solve [
  pick fresh y; repeat spec y;
  match goal with [ H3 : forall P3 P4 x0 phi0, _ |- _ ] => 
  specialize (H3 P1 ((y ~ psi) ++ P2) x phi ltac:(eauto) ltac:(auto));
  rewrite erasure_open in H3; simpl in H3;
  rewrite <- fv_open_lower in H3;
  auto end].

  all: try (destruct (q_leb q_Top psi); simpl).
  all: try (eapply notin_union).
  all: eauto.

  all: try solve [pick fresh y; repeat spec y;
  match goal with [ H3 : forall P3 P4 x0 phi0, _ |- _ ] => 
  specialize (H3 P1 ((y ~ psi) ++ P2) _ _ ltac:(reflexivity) ltac:(assumption));
  rewrite erasure_open in H3; simp_syntax_in H3;
  rewrite <- fv_open_lower in H3;
  auto end].

Admitted.
(* fix up with more fv rewrite lemmas *)
  
  

Lemma Grade_substitution_erasure : 
      (forall P psi b, 
          Grade P psi b -> forall P1 P2 x phi, 
            P = P2 ++ [(x,phi)] ++ P1 
            -> not (phi <= psi)
            -> forall a1, (subst a1 x (erasure psi b)) = (erasure psi b)).
Proof.
  move: CGrade_Grade_fv_erasure => [_ h].
  intros. 
  rewrite subst_fresh_eq; eauto.
Qed.


Lemma open_erasure_irrel : 
  forall L P phi psi b, 
    (forall x, x `notin` L -> Grade (x ~ phi ++ P) psi (open b (a_Var_f x))) -> 
    not (phi <= psi) -> forall a1 a2, 
    open (erasure psi b) a1 = open (erasure psi b) a2.
Proof.
  intros.
  pick fresh y for (fv (erasure psi b) \u L).
  spec y.
  rewrite (subst_intro y _ a1); auto.
  rewrite (subst_intro y _ a2); auto.
  replace (a_Var_f y) with (erasure psi (a_Var_f y)). 2: { auto. }
  rewrite <- erasure_open.
  move: Grade_substitution_erasure => h2.
  move: (h2 _ _ _ H1) => h3.
  specialize (h3 P nil y _ ltac:(simpl; eauto) ltac:(eauto)).
  rewrite h3.
  rewrite h3.
  auto.
Qed.


(* lemmas about erasure *)


Lemma Canonical_element : 
  (forall P phi psi a1 a2, CEq P phi psi a1 a2 -> psi <= phi -> erasure phi a1 = erasure phi a2) /\
  (forall P phi a1 a2, GEq P phi a1 a2 -> erasure phi a1 = erasure phi a2).
Proof.
  apply CEq_GEq_mutual. 
  all: intros; simpl; auto.
  all: try rewrite H1.
  all: try rewrite H2.
  all: try solve [try rewrite H; try rewrite H0; auto].
  all: try rewrite (canonical_body _ _ _  H0).
  all: try rewrite (canonical_body _ _ _  H).
  all: try solve [destruct (q_leb q_Top psi) eqn: LT; auto; try done;
                  rewrite H0; eauto using leq_Top].
  all: destruct (q_leb psi0 psi) eqn:LE; try rewrite H; try rewrite H0; auto.
Qed.

Lemma Erasure_Indistinguishability :
  (forall P phi psi a, CGrade P phi psi a -> CEq P phi psi a (erasure phi a)) /\
  (forall P phi a, Grade P phi a -> GEq P phi a (erasure phi a)).
Proof.
  apply CGrade_Grade_mutual. 
  all: intros; simpl; auto.
  all: eauto.
  all: try fresh_apply_GEq x; repeat spec x; eauto.
  all: try (rewrite erasure_open in H1; simpl in H1; simpl_env in H1).
  all: auto.

Admitted.
(*
  all: try solve [
  destruct (q_leb psi0 psi) eqn: LT; auto;
  econstructor; eauto; eapply CEq_Nleq; eauto using CGrade_lc, Grade_uniq with lc;
  rewrite LT; done].

  destruct (q_leb q_Top psi) eqn: LT; auto;
  try fresh_apply_GEq x; repeat spec x; eauto;
  try (rewrite erasure_open in H1; simp_syntax_in H1; simpl_env in H1); auto.
  eapply CEq_Nleq; eauto using CGrade_lc, Grade_uniq with lc.
  rewrite LT; done.
  eapply CEq_Nleq; eauto lc.
  Unshelve. exact psi.
Qed. *)

Lemma Value_erasure : forall a psi, Value a -> Value (erasure psi a).
Proof.
  intros.
  inversion H; subst; simpl; eauto.
  + inversion H0; subst; simpl. 
    all: eauto with lc.
    all: apply erasure_lc with (psi := psi) in H2; simpl in H2.
    all: admit. (* econstructor; eauto using lc. *)
  + apply erasure_lc with (psi := psi) in H1; simpl in H1.
    destruct (q_leb q_Top psi) eqn:LE; eauto with lc.
  + destruct (q_leb psi0 psi) eqn:LE; eauto with lc.
  + destruct (q_leb psi0 psi) eqn:LE; eauto with lc.
  + eauto using erasure_lc.
  + eauto using erasure_lc.
Admitted.



Lemma Step_erasure : forall a b, Step a b -> forall P phi, Grade P phi a -> Step (erasure phi a) (erasure phi b).
Proof.
  intros a b S. induction S; intros.
  all: try match goal with 
      [ H : Grade ?P ?phi ?b |- _ ] => inversion H ; clear H; subst end.
  all: intros; simpl; eauto using erasure_lc.
  all: try solve [destruct (q_leb psi phi) eqn:LE; eauto using erasure_lc].
  all: try match goal with [ H : lc (_ _) |- _ ] => 
    apply erasure_lc with (psi := phi) in H end.
  all: try solve [simpl in *; eauto].
  all: destruct (q_leb psi phi) eqn:LE.
  all: try invert_CGrade b; try done. 
  all: eauto with lc.
  all: try rewrite erasure_open.

  + destruct (q_leb q_Top phi) eqn:LT.
    eapply S_Beta; eauto with lc.
    simpl in H0. rewrite LT in H0. auto.
    eapply S_Beta; eauto with lc.
    simpl in H0. rewrite LT in H0. auto.
  + rewrite LE in H2. done. 
  + invert_Grade; subst.
    simpl in H0.
    erewrite -> open_erasure_irrel with (a2 := a_TmUnit); eauto.
    destruct (q_leb q_Top phi) eqn:LT.
    eapply S_Beta; eauto with lc.
    eapply S_Beta; eauto with lc.
  + simpl in H. rewrite LE in H.
    destruct (q_leb q_Bot phi) eqn:LT.
    eapply S_LetPairBeta; auto with lc.
    move: (leq_Bot phi)  => h. rewrite LT in h. done.
  + simpl in H. rewrite LE in H.
    destruct (q_leb q_Bot phi) eqn:LT.
    erewrite -> open_erasure_irrel with (a2 := a_TmUnit); eauto with lc.
    rewrite LE. done.
    move: (leq_Bot phi)  => h. rewrite LT in h. done.
Qed.    
      
