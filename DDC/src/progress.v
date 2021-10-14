Require Export Qual.tactics.
Require Export Qual.typing.
Require Export Qual.consist.

Set Implicit Arguments.
Open Scope grade_scope.

Lemma Consistent_Type : forall s A0,
    Consistent (a_Type s) A0 -> ValueType A0 -> A0 = (a_Type s).
Proof.
  intros s A0 C V.
  destruct A0; 
    simpl in *; inversion C; inversion V.
  all: subst; auto.
  all: done.
Qed.

Ltac impossible_defeq := 
  let h0 := fresh in
  let VT := fresh in
  let VT2 := fresh in       
       match goal with 
    [ E : DefEq ?nil ?q ?A ?B |- _ ] => 
       pose h0:= E; clearbody h0;
       eapply DefEq_Consistent in h0; eauto;
       move: (DefEq_lc1 E) => l0;
       move: (DefEq_lc2 E) => l1;
       inversion l0; inversion l1; subst;
       have VT: ValueType A; eauto;
       have VT2 : ValueType B; eauto;
       inversion h0; subst;
       eauto; try done end.


Lemma Canonical_Pi' : forall b psi psi0 B A1 A2, 
    Typing nil psi b B -> 
    DefEq nil q_C B (a_Pi psi0 A1 A2) -> Value b -> exists A0 a0, b = a_Abs psi0 A0 a0.
Proof. intros b psi psi0 B A1 A2 T E V.
       dependent induction T.
       all: try solve
         [inversion V; match goal with [ H : ValueType ?a |- _ ] => inversion H end].

       impossible_defeq.

       (* conversion case *)
       simpl in *;
       destruct IHT1; auto;
       try eapply Eq_Trans with (b := B); auto using Eq_Sym;
       eauto.
       
       all: impossible_defeq.
Qed.

Lemma Canonical_Pi : forall b psi psi0 A1 A2, 
    Typing nil psi b (a_Pi psi0 A1 A2) -> 
    Value b -> exists A0 a0, b = a_Abs psi0 A0 a0.
Proof. 
  intros.
  eapply Canonical_Pi' in H; auto. 
  2: { eapply Eq_Refl. 
       replace nil with (labels nil). 2: auto.
       apply Typing_regularity in H; auto. destruct H.
       eapply Typing_Grade.
       replace nil with (meet_ctx_l q_C nil); eauto. 
  } 
  auto.
Qed.

Lemma Canonical_WSigma' : forall b psi psi0 B A1 A2, 
    Typing nil psi b B -> 
    DefEq nil q_C B (a_WSigma psi0 A1 A2) -> Value b -> exists a0 a1, b = a_WPair a0 psi0 a1.
Proof. intros b psi psi0 B A1 A2 T E V.
       dependent induction T.
       all: try solve
         [inversion V; match goal with [ H : ValueType ?a |- _ ] => inversion H end].

       impossible_defeq.

       (* conversion case *)
       simpl in *;
       destruct IHT1; auto;
       try eapply Eq_Trans with (b := B); auto using Eq_Sym;
       eauto.
       
       all: impossible_defeq.
Qed.

Lemma Canonical_WSigma : forall b psi psi0 A1 A2, 
    Typing nil psi b (a_WSigma psi0 A1 A2) -> 
    Value b -> exists a0 a1, b = a_WPair a0 psi0 a1.
Proof. 
  intros.
  eapply Canonical_WSigma' in H; auto. 
  2: { eapply Eq_Refl. 
       replace nil with (labels nil). 2: auto.
       apply Typing_regularity in H; auto. destruct H.
       eapply Typing_Grade.
       replace nil with (meet_ctx_l q_C nil); eauto.
  } 
  auto.
Qed.

Lemma Canonical_SSigma' : forall b psi psi0 B A1 A2, 
    Typing nil psi b B -> 
    DefEq nil q_C B (a_SSigma psi0 A1 A2) -> Value b -> exists a0 a1, b = a_SPair a0 psi0 a1.
Proof. intros b psi psi0 B A1 A2 T E V.
       dependent induction T.
       all: try solve
         [inversion V; match goal with [ H : ValueType ?a |- _ ] => inversion H end].

       impossible_defeq.

       (* conversion case *)
       simpl in *;
       destruct IHT1; auto;
       try eapply Eq_Trans with (b := B); auto using Eq_Sym;
       eauto.
       
       all: impossible_defeq.
Qed.

Lemma Canonical_SSigma : forall b psi psi0 A1 A2, 
    Typing nil psi b (a_SSigma psi0 A1 A2) -> 
    Value b -> exists a0 a1, b = a_SPair a0 psi0 a1.
Proof. 
  intros.
  eapply Canonical_SSigma' in H; auto. 
  2: { eapply Eq_Refl. 
       replace nil with (labels nil). 2: auto.
       apply Typing_regularity in H; auto. destruct H.
       eapply Typing_Grade.
       replace nil with (meet_ctx_l q_C nil); eauto.
  } 
  auto.
Qed.

Lemma Canonical_Sum' : forall b psi B A1 A2, 
    Typing nil psi b B -> 
    DefEq nil q_C B (a_Sum A1 A2) -> Value b -> exists a0, b = a_Inj1 a0 \/ b = a_Inj2 a0.
Proof. intros b psi B A1 A2 T E V.
       dependent induction T.
       all: try solve
         [inversion V; match goal with [ H : ValueType ?a |- _ ] => inversion H end].

       impossible_defeq.

       (* conversion case *)
       simpl in *;
       destruct IHT1; auto;
       try eapply Eq_Trans with (b := B); auto using Eq_Sym;
       eauto.
       
       all: impossible_defeq.
Qed.

Lemma Canonical_Sum : forall b psi A1 A2, 
    Typing nil psi b (a_Sum A1 A2) -> 
    Value b -> exists a0, b = a_Inj1 a0 \/ b = a_Inj2 a0.
Proof. 
  intros.
  eapply Canonical_Sum' in H; auto. 
  eapply Eq_Refl. 
  replace nil with (labels nil). 2: auto.
  apply Typing_regularity in H; auto. destruct H.
  eapply Typing_Grade.
  replace nil with (meet_ctx_l q_C nil); eauto.
Qed.

Lemma Typing_progress: 
  forall psi a A, Typing nil psi a A -> (exists a', Step a a') \/ Value a.
Proof.
  intros. 
  move: (Typing_lc1 H) => LC.
  dependent induction H.
  all: try solve [right; eauto using Typing_lc1].
  all: repeat match goal with [ H : _ ~= _ -> _ |- _ ] => specialize (H ltac:(reflexivity)) end.
  all: try solve [auto].
  all: try solve [match goal with [H : binds _ _ _ |- _ ] => inversion H end].

  all: inversion LC; subst.
  - (* Abs *) 
    right. eauto.
  - (* AppRel *)
    left.
    destruct IHTyping1 as [[a' S]|V]; auto.
    + eauto.
    + move: (Canonical_Pi H V) => [A0 [a0 EQ]]. subst.
      inversion H4.
      eexists.
      eapply S_Beta; eauto.
  - (* AppIrrel *)
    left.
    destruct IHTyping1 as [[a' S]|V]; auto.
    + eauto.
    + move: (Canonical_Pi H V) => [A0 [a0 EQ]]. subst.
      inversion H4.
      eexists.
      eapply S_Beta; eauto.
  - (* LetPair *)
    left.
    destruct IHTyping  as [[a' S]|V]; auto.
    + eexists.
      eapply S_LetPairCong; eauto.
    + move: (Canonical_WSigma H1 V) => [a0 [a1 EQ]]. subst.
      match goal with [ H6 : lc_tm (a_WPair _ _ _) |- _ ] => inversion H6 end.
      eexists. 
      eapply S_LetPairBeta; eauto.
  - (* Proj1 *)
    left.
    destruct IHTyping  as [[a' S]|V]; auto.
    + eexists. eauto.
    + move: (Canonical_SSigma H V) => [a0 [a1 EQ]]. subst.
      match goal with [ H6 : lc_tm (a_SPair _ _ _) |- _ ] => inversion H6 end.
      eexists. eauto.
  - (* Proj2 *)
    left.
    destruct IHTyping  as [[a' S]|V]; auto.
    + eexists. eauto.
    + move: (Canonical_SSigma H V) => [a0 [a1 EQ]]. subst.
      match goal with [ H6 : lc_tm (a_SPair _ _ _) |- _ ] => inversion H6 end.
      eexists. eauto.
  - (* Case *)
    left.
    destruct IHTyping1 as [[a' S]|V]; auto.
    + eexists. eauto.
    + move: (Canonical_Sum H1 V) => [a0 [EQ1 | EQ2]];
        subst.
      match goal with [ H6 : lc_tm (a_Inj1 _) |- _ ] => inversion H6 end.
      eexists. eauto.
      match goal with [ H6 : lc_tm (a_Inj2 _) |- _ ] => inversion H6 end.
      eexists. eauto.
Qed.

