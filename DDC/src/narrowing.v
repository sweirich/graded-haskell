Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels. 
Require Export Qual.uniq. 

Set Implicit Arguments.
Open Scope grade_scope.


Lemma Grade_narrowing : (forall P psi phi a, CGrade P psi phi a -> forall P', P_sub P' P -> CGrade P' psi phi a) /\
  (forall P psi a, Grade P psi a -> forall P', P_sub P' P -> Grade P' psi a).
Proof. 
  apply CGrade_Grade_mutual.
  all : intros; eauto using P_sub_uniq1.
  all: try solve [fresh_apply_Grade x; eauto;
    repeat spec x;
    match goal with [H2 : forall P', _ |- _ ] => eapply H2 end;
    econstructor; eauto;
    reflexivity].
  - (* Var *)
    move: (P_sub_binds _ _ ltac:(eassumption) b) => [psi' [bb ss]]. 
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

Lemma DefEq_narrowing : 
(forall P phi psi a b,
  CDefEq P phi psi a b -> forall P', P_sub P' P -> CDefEq P' phi psi a b) /\
(forall P phi a b,
  DefEq P phi a b -> forall P', P_sub P' P -> DefEq P' phi a b).
Proof.
  move: (Grade_narrowing) => [ _ gn].
  eapply CDefEq_DefEq_mutual.
  all: intros P phi a b h.
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
  eapply Eq_Beta; eauto.
  eapply Eq_App; eauto. 
  eapply Eq_PiSnd; eauto.
  eapply Eq_WSigmaSnd; eauto.
  eapply Eq_WPair; eauto.
  eapply Eq_SSigmaSnd; eauto.
  eapply Eq_SPair; eauto.
  eapply Eq_Sum; eauto.
  eapply Eq_Case; eauto.

Qed.

Lemma Par_narrowing : 
  (  forall P1 psi phi a b, CPar P1 psi phi a b -> forall P2, P_sub P2 P1 -> CPar P2 psi phi a b) /\
  forall P1 psi a b, Par P1 psi a b -> forall P2, P_sub P2 P1 -> Par P2 psi a b.
Proof. 
  move: (Grade_narrowing) => [_ gn].
  apply CPar_Par_mutual.
  all: intros.
  all: eauto using Grade_narrowing, GEq_narrowing.
  all: try (fresh_apply_Par x; eauto; repeat spec x).
  all: try solve [eapply H0; econstructor; eauto; try reflexivity].
  all: try solve [eapply H; econstructor; eauto; try reflexivity].
  eapply CPar_Nleq; eauto using P_sub_uniq1.
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
                 match goal with [H4 : forall W, _ -> Typing _ _ _ _ |- _ ] =>                  
                 eapply H4 end;
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
    + clear H2 H3. repeat spec x. eapply H0; econstructor; eauto. 
      reflexivity. eapply ctx_sub_meet_ctx_l; auto.
      rewrite dom_meet_ctx_l. auto.
      rewrite dom_meet_ctx_l. auto.
    + move=> y Fry.
      clear H H0 H2.
      spec x. spec y.
      eapply H3. econstructor; eauto. reflexivity.
  - (* SPair *)
    eapply T_SPair...
  - (* case *)
    fresh_apply_Typing x; eauto using po_join_r, ctx_sub_meet_ctx_l.
    repeat spec x.
    eapply H0.
    econstructor; eauto; try reflexivity.
    eapply ctx_sub_meet_ctx_l; auto.
    rewrite dom_meet_ctx_l. auto.
    rewrite dom_meet_ctx_l. auto.
Qed.
