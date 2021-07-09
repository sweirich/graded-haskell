Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels. 
Require Export Qual.uniq. 

Set Implicit Arguments.
Open Scope grade_scope.


Lemma Grade_narrowing : forall P psi a, Grade P psi a -> forall P', P_sub P' P -> Grade P' psi a.
Proof. 
  intros P psi a H. 
  induction H.
  all : intros; eauto using P_sub_uniq1.
  all: try solve [fresh_apply_Grade x; eauto;
    repeat spec x;
    match goal with [H2 : forall P', _ |- _ ] => eapply H2 end;
    econstructor; eauto;
    reflexivity].
  - (* Var *)
    move: (P_sub_binds _ _ H2 H1) => [psi' [b ss]]. clear H1.
    eapply G_Var. 3 : { eauto. } eauto using P_sub_uniq1.
    transitivity psi0; auto.
Qed.

Lemma CEq_GEq_narrowing : 
  (forall P phi phi0 a b,
  CEq P phi phi0 a b -> forall P', P_sub P' P -> CEq P' phi phi0 a b) /\
  (forall P phi a b,
  GEq P phi a b -> forall P', P_sub P' P -> GEq P' phi a b).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; eauto using P_sub_uniq1.
  all: try solve [fresh_apply_GEq x; eauto;
    repeat spec x;
    match goal with [ H : forall P', P_sub P' ?P -> _ |- _] => eapply H end;
    econstructor; eauto;
    reflexivity] .
  - eapply P_sub_binds in b; eauto.
    destruct b as [psi' [b ss]].
    eapply GEq_Var; eauto using P_sub_uniq1.
    transitivity psi0; auto.   
Qed.

Lemma GEq_narrowing : forall P phi a b,
  GEq P phi a b -> forall P', P_sub P' P -> GEq P' phi a b.
Proof. apply CEq_GEq_narrowing; eauto. Qed.

Lemma DefEq_narrowing : forall P phi a b,
  DefEq P phi a b -> forall P', P_sub P' P -> DefEq P' phi a b.
Proof.
  intros P phi a b h.
  move: (Grade_narrowing) => gn.
  induction h.
  all: intros; eauto 3 using P_sub_uniq1.
  all: try solve [fresh_apply_DefEq x; auto;
    repeat spec x;
    match goal with [ H : forall P', P_sub P' ?P -> _ |- _] => eapply H end;
    econstructor; eauto;
    reflexivity].

  all: try solve [pick fresh x and apply Eq_SubstIrrel; eauto 2;
    repeat spec x;
    match goal with [ H : forall P', P_sub P' ?P -> _ |- _] => eapply H end;
    econstructor; eauto;
    reflexivity].

  eapply Eq_Trans; eauto.
  eapply Eq_Sym; eauto.
  eapply Eq_AppRel; eauto. 
  eapply Eq_PiSnd; eauto.
  eapply Eq_WSigmaSnd; eauto.
  eapply Eq_WPairRel; eauto.
  eapply Eq_SSigmaSnd; eauto.
  eapply Eq_SPairRel; eauto.
  eapply Eq_Sum; eauto.
  eapply Eq_Case; eauto.

Qed.

Lemma Par_narrowing : 
  forall P1 psi a b, Par P1 psi a b -> forall P2, P_sub P2 P1 -> Par P2 psi a b.
Proof. 
  intros P1 psi a b H. induction H; intros.
  all: eauto using Grade_narrowing, GEq_narrowing.
  all: try (fresh_apply_Par x; auto; repeat spec x).
  all: try solve [eapply H3; econstructor; eauto; try reflexivity].
  
  eapply H2. econstructor; eauto; try reflexivity.
Qed.


Lemma Typing_narrowing : forall psi a A W1, 
    Typing W1 psi a A ->
    forall W2, ctx_sub W2 W1 ->
    Typing W2 psi a A.
Proof with eauto using ctx_sub_meet_ctx_l.
  induction 1; intros...
  all: try  move: (ctx_sub_uniq ltac:(eassumption) ltac:(eassumption)) => uu. 
  all: eauto 3.
  all: try solve [
                 fresh_apply_Typing x; 
                 eauto using po_join_r, ctx_sub_meet_ctx_l;
                 repeat spec x;
                 eapply H3;
                 econstructor; eauto;
                 reflexivity ].
  - (* conv *)
    have S: ctx_sub (meet_ctx_l q_C W2) (meet_ctx_l q_C W). eauto... 
    move: (ctx_sub_labels S) => Eq. 
    eapply T_Conv; eauto 2.
    eapply DefEq_narrowing; eauto.
  - (* Var *)
    move: (ctx_sub_binds ltac:(eauto) ltac:(eauto)) => [psi1 [h1 h2]].
    eapply T_Var with (psi0 := psi1); eauto using ctx_sub_uniq.
    transitivity psi0; auto.
  - (* WPair *)
    eapply T_WPair...
  - (* WPairI *)
    eapply T_WPairIrrel...
  - (* LetPair *)
    fresh_apply_Typing x; 
    eauto using po_join_r, ctx_sub_meet_ctx_l.
    + clear H2 H3. repeat spec x. eapply H2; econstructor; eauto. 
      reflexivity. eapply ctx_sub_meet_ctx_l; auto.
      rewrite dom_meet_ctx_l. auto.
      rewrite dom_meet_ctx_l. auto.
    + move=> y Fry.
      clear H H0 H2.
      spec x. spec y.
      eapply H0. econstructor; eauto. reflexivity.
  - (* SPair *)
    eapply T_SPair...
  - (* case *)
    fresh_apply_Typing x; eauto using po_join_r, ctx_sub_meet_ctx_l.
    repeat spec x.
    eapply H2.
    econstructor; eauto; try reflexivity.
    eapply ctx_sub_meet_ctx_l; auto.
    rewrite dom_meet_ctx_l. auto.
    rewrite dom_meet_ctx_l. auto.
Qed.
