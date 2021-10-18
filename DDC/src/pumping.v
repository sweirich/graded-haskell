Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels.
Require Export Qual.narrowing.

Set Implicit Arguments.
Open Scope grade_scope.


(* ---------- grade ---------- *)

Ltac pumping_ih := 
    match goal with 
      [ H3 : forall P3 x0 psi1 P4, 
           [(?y, ?psi2)] ++ ?P2 ++ [(?x, ?psi0)] ++ ?P1 = P3 ++ [(x0, psi1)] ++ P4 -> _ |-  _ ] => 
      specialize (H3 ([(y, psi2)] ++ P2) x psi0 P1 ltac:(simpl_env; eauto) _ ltac:(eassumption)); simpl_env in H3 end.


Lemma CGrade_Grade_pumping_middle : 
  (forall P psi phi0 b1 ,
  CGrade P psi phi0 b1  ->  forall P2 x psi0 P1, 
        P = P2 ++ [(x,psi0)] ++ P1 
       -> forall psi1, psi1 <= psi -> CGrade (P2 ++ [(x,psi0 * psi1)] ++ P1) psi phi0 b1) /\
  (forall P psi b1,
  Grade P psi b1  -> forall P2 x psi0 P1, 
        P = P2 ++ [(x,psi0)] ++ P1 
       -> forall psi1, psi1 <= psi -> Grade (P2 ++ [(x,psi0 * psi1)] ++ P1) psi b1 ).
Proof. 
  apply CGrade_Grade_mutual.
  all: intros; subst; eauto. 
  all: try solve [econstructor; eauto using helper_uniq].
  all: try solve [fresh_apply_Grade y; auto; repeat spec y; pumping_ih; eauto].
  - destruct (x == x0).
  ++ subst. 
     apply binds_mid_eq in b; auto. 
     subst.
     eapply G_Var with (psi0 := psi1 * psi2); eauto using helper_uniq.
     eapply join_lub; eauto.
  ++ eapply G_Var with (psi0 := psi0); eauto using helper_uniq.
Qed.

Lemma Grade_pumping_middle : forall P2 x psi0 P1 psi b, 
  Grade (P2 ++ x ~ psi0 ++ P1) psi b -> forall psi1, psi1 <= psi -> Grade (P2 ++ x ~ psi0 * psi1 ++ P1) psi b.
Proof. 
  intros. eapply CGrade_Grade_pumping_middle; eauto.
Qed.

Lemma Grade_pumping : forall psi y psi0 psi1 P a, psi <= psi1  ->
  Grade ([(y, psi0)] ++ P) psi1 a ->
  Grade ([(y, psi0 * psi)] ++ P) psi1 a.
Proof. 
  intros.
  move: (@Grade_pumping_middle nil y psi0 P psi1 a) => N2.
  simpl_env in N2.
  eauto.
Qed. 

(* -------------------- geq --------------- *)

Lemma CEq_GEq_pumping_middle : 
  (forall P psi phi0 b1 b2,
  CEq P psi phi0 b1 b2 ->  forall P2 x psi0 P1, 
        P = P2 ++ [(x,psi0)] ++ P1 
       -> forall psi1, psi1 <= psi -> CEq (P2 ++ [(x,psi0 * psi1)] ++ P1) psi phi0 b1 b2) /\
  (forall P psi b1 b2,
  GEq P psi b1 b2 -> forall P2 x psi0 P1, 
        P = P2 ++ [(x,psi0)] ++ P1 
       -> forall psi1, psi1 <= psi -> GEq (P2 ++ [(x,psi0 * psi1)] ++ P1) psi b1 b2).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; subst; eauto.  
  all: try solve [econstructor; eauto using helper_uniq].
  all: try solve [
    fresh_apply_GEq y; eauto; repeat spec y;
    match goal with [ H3 : forall P3 x0 psi0 Pr, _ = _ -> _ |- _ ] => 
    specialize (H3 ([(y, q_C)] ++ P2) x psi1 P1 ltac:(simpl_env; eauto)
                                                              _ ltac:(eassumption)); simpl_env in H3 end;
    eauto].

  - (* var *)
    destruct (x == x0).
    ++ subst.
     apply binds_mid_eq in b; auto. 
     subst.
     eapply GEq_Var with (psi0 := psi1 * psi2); eauto using helper_uniq.
     eapply join_lub; eauto.
  ++ eapply GEq_Var with (psi0 := psi0); eauto using helper_uniq.
  - (* Pi *)
    fresh_apply_GEq y; eauto; repeat spec y.
    match goal with [ H3 : forall P3 x0 psi2 P4, [(?y,?psi0)] ++ ?P2 ++ [(?x, ?psi1)] ++ ?P1 = _ -> _ |- _ ] => 
    specialize (H3 ([(y, psi0)] ++ P2) x psi1 P1 ltac:(simpl_env; eauto)
                                                              _ ltac:(eassumption)); simpl_env in H3 end;
    eauto.
    
  - (* Abs *) 
    fresh_apply_GEq y; eauto; repeat spec y.
    match goal with [ H3 : forall P3 x0 psi2 P4, [(?y,?psi0)] ++ ?P2 ++ [(?x, ?psi1)] ++ ?P1 = _ -> _ |- _ ] => 
    specialize (H3 ([(y, psi0)] ++ P2) x psi1 P1 ltac:(simpl_env; eauto)
                                                              _ ltac:(eassumption)); simpl_env in H3 end;
    eauto.

  - (* WSigma *)
    fresh_apply_GEq y; eauto; repeat spec y.
    match goal with [ H3 : forall P3 x0 psi2 P4, [(?y,?psi0)] ++ ?P2 ++ [(?x, ?psi1)] ++ ?P1 = _ -> _ |- _ ] => 
    specialize (H3 ([(y, psi0)] ++ P2) x psi1 P1 ltac:(simpl_env; eauto)
                                                              _ ltac:(eassumption)); simpl_env in H3 end;
    eauto.


  - (* LetPair *) 
    fresh_apply_GEq y; eauto; repeat spec y.
    match goal with [ H3 : forall P3 x0 psi2 P4, [(?y,?psi0)] ++ ?P2 ++ [(?x, ?psi1)] ++ ?P1 = _ -> _ |- _ ] => 
    specialize (H3 ([(y, psi0)] ++ P2) x psi1 P1 ltac:(simpl_env; eauto)
                                                              _ ltac:(eassumption)); simpl_env in H3 end;
    eauto.

 - (* SSigma *)
    fresh_apply_GEq y; eauto; repeat spec y.
    match goal with [ H3 : forall P3 x0 psi2 P4, [(?y,?psi0)] ++ ?P2 ++ [(?x, ?psi1)] ++ ?P1 = _ -> _ |- _ ] => 
    specialize (H3 ([(y, psi0)] ++ P2) x psi1 P1 ltac:(simpl_env; eauto)
                                                              _ ltac:(eassumption)); simpl_env in H3 end;
    eauto.

Qed.

Lemma GEq_pumping : forall P1 x psi0 psi1 psi b1 b2,
  GEq ([(x,psi0)] ++ P1)  psi b1 b2 -> 
  psi1 <= psi -> 
  GEq ([(x,psi0 * psi1)] ++ P1) psi b1 b2.
Proof. 
  intros.
  eapply CEq_GEq_pumping_middle with (P2 := nil); eauto.
Qed.

(* -------------- defeq --------------- *)

Lemma CDefEq_DefEq_pumping_middle : 
(forall P psi phi b1 b2,
  CDefEq P psi phi b1 b2 -> forall P2 x psi0 P1, 
        P = P2 ++ [(x,psi0)] ++ P1 
       -> forall psi1, psi1 <= psi -> CDefEq (P2 ++ [(x,psi0 * psi1)] ++ P1) psi phi b1 b2) /\
forall P psi b1 b2,
  DefEq P psi b1 b2 -> forall P2 x psi0 P1, 
        P = P2 ++ [(x,psi0)] ++ P1 
       -> forall psi1, psi1 <= psi -> DefEq (P2 ++ [(x,psi0 * psi1)] ++ P1) psi b1 b2.
Proof with  eauto 3 using Grade_pumping_middle, helper_uniq.  
  apply CDefEq_DefEq_mutual.
  all: intros; subst...

  (* Pi / Abs / WSigma / SSigma / LetPair *)
  all: try solve [fresh_apply_DefEq y; auto; repeat spec y;
  match goal with [ H3 : forall P3 x0 psi2 P4, [(?y,?psi0)] ++ ?P2 ++ [(?x, ?psi1)] ++ ?P1 = _ -> _ |- _ ] => 
                  specialize (H3 ([(y, psi0)] ++ P2) x psi1 P1 ltac:(simpl_env; eauto)
                                                              _ ltac:(eassumption)); simpl_env in H3 end;
  auto]. 

  eapply Eq_Trans...
  eapply Eq_Beta...
  eapply Eq_App...
  eapply Eq_PiSnd...
  eapply Eq_WSigmaSnd...
  eapply Eq_WPair...
  eapply Eq_SSigmaSnd...
  eapply Eq_SPair...
  eapply Eq_Sum...
  eapply Eq_Case...

  pick fresh y and apply Eq_Subst; eauto 1; repeat spec y.
  specialize (H3 ([(y, psi)] ++ P2) x psi0 P1 ltac:(simpl_env; eauto) _ ltac:(eassumption)). 
  simpl_env in H3; eauto.
  eauto...
Qed.

Lemma DefEq_pumping_middle : 
forall P psi b1 b2,
  DefEq P psi b1 b2 -> forall P2 x psi0 P1, 
        P = P2 ++ [(x,psi0)] ++ P1 
       -> forall psi1, psi1 <= psi -> DefEq (P2 ++ [(x,psi0 * psi1)] ++ P1) psi b1 b2.
Proof. apply CDefEq_DefEq_pumping_middle. Qed.

Lemma DefEq_pumping : forall P1 x psi0 psi1 psi b1 b2,
  DefEq ([(x,psi0)] ++ P1)  psi b1 b2 -> 
  psi1 <= psi -> 
  DefEq ([(x,psi0 * psi1)] ++ P1) psi b1 b2.
Proof. 
  intros.
  eapply CDefEq_DefEq_pumping_middle with (P2 := nil); eauto.
Qed.

(* --------------- typing ------------ *)


Lemma Typing_leq_C : forall W psi a A, Typing W psi a A -> psi <= q_C.
Proof. 
  intros W psi a A h.
  induction h; intros; subst; simpl; simpl_env; auto.
  pick fresh x; repeat spec x; auto.
Qed.


Local Ltac Typing_mult_ih :=
match goal with 
      [ H3 : forall x0 psi2 A1 W3 W4 , 
           [(?y, (?psi1, ?A0))] ++ ?W2 ++ [(?x, (?psi0, ?A))] ++ ?W1 ~= W3 ++ [(x0, (psi2, A1))] ++ W4 -> _ |-  _ ] => 
      specialize (H3 x psi0 A ([(y, (psi1, A0))] ++ W2) W1 ltac:(simpl_env; eauto) ltac:(eassumption))
      ; simpl_env in H3 ; auto end.


Lemma join_ctx_r_ctx_sub : forall W q, uniq W ->  ctx_sub W (join_ctx_r q W).
intros. induction W; simpl; eauto. destruct a. destruct p.
destruct_uniq. econstructor; eauto.
eapply leq_join_l. unfold join_ctx_r.  auto.
Qed.

Lemma Typing_pumping_middle : forall x psi0 A W2 W1 psi b B psi1, 
  Typing (W2 ++ [(x, (psi0, A))] ++ W1) psi b B ->
  psi1 <= psi ->
  Typing (W2 ++ [(x, (psi0 * psi1, A))] ++ W1) psi b B.
Proof. 
  intros.
  dependent induction H; intros.
  all: try solve [econstructor; eauto 2 using helper_uniq].
  all: try solve [fresh_apply_Typing y; eauto; repeat spec y; Typing_mult_ih].
  all: have LTC: (psi1 <= q_C) by transitivity psi; eauto using Typing_leq_C.
  - (* conversion case *) 
    simpl_env in *.
    eapply T_Conv; simpl_env; try rewrite meet_mult; auto.
    eauto using DefEq_pumping_middle.
  - destruct (x == x0).
    ++ subst.
       match goal with [ H1 : binds _ _ _ |- _ ] => apply binds_mid_eq in H1; auto end.
       invert_equality.
       eapply T_Var with (psi0 := psi0 * psi1); eauto using helper_uniq.
       eapply join_lub; eauto.
    ++ eapply Typing_narrowing with (W1 := (join_ctx_r psi1 (W2 ++ [(x,(psi0,A))] ++ W1))).
       eapply binds_map with (f := fun '(p,A) => (p * psi1, A)) in H1.
       eapply T_Var with (psi0 := psi2 * psi1).
       unfold join_ctx_r. eauto using helper_uniq.
       eapply join_lub; eauto.
       unfold join_ctx_r. auto. auto.
       destruct_uniq.
       unfold join_ctx_r. simpl_env.
       eapply ctx_sub_app. eapply join_ctx_r_ctx_sub; eauto.
       eapply ctx_sub_app. econstructor; eauto. reflexivity. 
       eapply join_ctx_r_ctx_sub; eauto.
       solve_uniq.
       solve_uniq.
  - (* abs case *)
    fresh_apply_Typing y; eauto using helper_uniq; repeat spec y. Typing_mult_ih.
    simpl_env; try rewrite meet_mult; simpl_env; eauto.
    eapply IHTyping; simpl_env; eauto.
  - eapply T_App; eauto.
    eapply IHTyping2; eauto.
    transitivity psi; eauto using leq_join_r.
  - eapply T_AppIrrel; eauto.
    simpl_env; try rewrite meet_mult; auto.
    eapply IHTyping2; simpl_env; eauto.
  - eapply T_WPair; simpl_env; try rewrite meet_mult; eauto.
    eapply IHTyping1; simpl_env; eauto.
    eapply IHTyping2; eauto.
    transitivity psi; eauto using leq_join_r.
  - eapply T_WPairIrrel; simpl_env; try rewrite meet_mult; eauto.
    eapply IHTyping1; simpl_env; eauto.
    eapply IHTyping2; simpl_env; eauto.
  - (* letpair *) 
    fresh_apply_Typing y; eauto 3 using helper_uniq. 
    + specialize (H0 y ltac:(auto)).
      match goal with 
          [ H3 : forall x0 psi3 A1 W3 W4 , 
           [(?y, (?psi1, ?A0))] ++ meet_ctx_l q_C (?W2 ++ [(?x, (?psi0, ?A))] ++ ?W1) ~= 
           W3 ++ [(x0, (psi3, A1))] ++ W4 -> _ |-  _ ] => 
      specialize (H3 x (q_C + psi0) A ([(y, (psi1, A0))] ++ meet_ctx_l q_C W2) (meet_ctx_l q_C W1)
                 ltac:(simpl_env; eauto) ltac:(eassumption)) 
      ; simpl_env in H3 ; auto end.
    simpl_env; try rewrite meet_mult; simpl_env; eauto.
    + move=> z FrZ.
      specialize (H3 y ltac:(auto) z ltac:(auto)).
      Typing_mult_ih.
  - eapply T_SPair; simpl_env; try rewrite meet_mult; eauto.
    eapply IHTyping1; simpl_env; eauto.
    eapply IHTyping2; eauto.
    transitivity psi; eauto using leq_join_r.
  - (* inj1 *)
    eapply T_Inj1; simpl_env; try rewrite meet_mult; eauto.
    eapply IHTyping2; simpl_env; eauto.
  - (* inj2 *)
    eapply T_Inj2; simpl_env; try rewrite meet_mult; eauto.
    eapply IHTyping2; simpl_env; eauto.
  - (* case *) 
    fresh_apply_Typing y; eauto 3 using helper_uniq.
    repeat spec y.
    match goal with 
          [ H3 : forall x0 psi3 A1 W3 W4 , 
           [(?y, (?psi1, ?A0))] ++ meet_ctx_l q_C (?W2 ++ [(?x, (?psi0, ?A))] ++ ?W1) ~= 
           W3 ++ [(x0, (psi3, A1))] ++ W4 -> _ |-  _ ] => 
      specialize (H3 x (q_C + psi0) A ([(y, (psi1, A0))] ++ meet_ctx_l q_C W2) (meet_ctx_l q_C W1)
                 ltac:(simpl_env; eauto) ltac:(eassumption)) 
      ; simpl_env in H3 ; auto end.
    simpl_env; try rewrite meet_mult; simpl_env; eauto.
Qed.    

Lemma Typing_pumping : forall x psi0 A W psi b B psi1, 
    psi1 <= psi ->
    Typing ([(x, (psi0, A))] ++ W) psi b B ->
    Typing ([(x, (psi0 * psi1, A))] ++ W) psi b B.
Proof. 
  intros.
  eapply Typing_pumping_middle with (W2 := nil); eauto.
Qed.

