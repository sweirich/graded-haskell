Require Export Qual.grade. 
Require Export Qual.defeq.
Require Export Qual.labels.
Require Export Qual.narrowing.
Require Export Qual.uniq.
Require Export Qual.subst.
Require Export Qual.consist.
Require Export Qual.pumping.
Require Export Qual.typing_ctx_fv.

Set Implicit Arguments.
Open Scope grade_scope.



(* -------------------------------------- *)

Lemma Typing_Grade : forall W psi a A, Typing W psi a A -> Grade (labels W) psi a.
Proof. 
  intros W psi a A h.
  induction h; intros; subst; simpl; simpl_env; auto.
  all: try solve [fresh_apply_Grade x; auto;
    repeat spec x;
    match goal with [ H2 : Grade _ _ _ |- _ ] => simpl in H2; simpl_env in H2 end;
    eauto].
  - (* Var *)
    eapply G_Var with (psi0 := psi0); eauto using leq_join_r. 
  - (* Abs *)
    fresh_apply_Grade x; auto; repeat spec x.
    simpl_env in H1.
    move: (Grade_uniq H1) => u. destruct_uniq.
    eapply Grade_narrowing; eauto. econstructor; eauto using leq_join_l, P_sub_refl, Typing_uniq. 
    inversion IHh. subst.
    pick fresh x. repeat spec x. 
    destruct (q_leb q_Top psi) eqn: LE.
    + assert (q_Top = psi). { apply q_leb_antisym; auto. eapply leq_Top. }
      subst. 
      eapply CG_Leq; eauto. 
    + eapply CG_Nleq; eauto using Grade_lc.
      rewrite LE. done.
      apply Grade_uniq in H2. simpl_env in H2. destruct_uniq. auto.
  - (* App *)
    eapply G_App; eauto.
    destruct (q_leb psi0 psi) eqn:LE.
    rewrite join_leq in IHh2. rewrite LE. auto. auto.
    eapply CG_Nleq; eauto using Typing_lc1, Grade_uniq. rewrite LE. done.
  - (* WPair *)
    destruct (q_leb psi0 psi) eqn:LE.
    eapply G_WPair; eauto. rewrite join_leq in IHh2. rewrite LE. auto. auto.
    eapply G_WPair; eauto.  eapply CG_Nleq; eauto using Typing_lc1, Grade_uniq. rewrite LE. done.
  - (* LetPair *)
    admit.
(*    fresh_apply_Grade x; auto; repeat spec x.
    pick fresh y. repeat spec y.
    eapply Grade_narrowing; eauto. 
    simpl; econstructor; eauto using leq_join_l, P_sub_refl, Typing_uniq.  *)
  - (* SPair *)
    destruct (q_leb psi0 psi) eqn:LE.
    eapply G_SPair; eauto. rewrite join_leq in IHh2. rewrite LE. auto. auto.
    eapply G_SPair; eauto.  eapply CG_Nleq; eauto using Typing_lc1, Grade_uniq. rewrite LE. done.
Admitted.



Lemma Typing_meet_ctx_l : forall W psi b B q, 
    Typing W psi b B ->
    Typing (meet_ctx_l q W) psi b B.
Proof.
  intros W psi b B q h. eapply Typing_narrowing; eauto.
  eapply meet_ctx_l_ctx_sub; eauto using Typing_uniq.
Qed.

Lemma Typing_subsumption : forall psi1 a A W, 
    Typing W psi1 a A ->
    forall psi2, psi1 <= psi2 -> 
    Typing W psi2 a A.
Proof.
  induction 1; intros.
  all: eauto 5 using leq_join_r.
  - (* var *)    
    eapply T_Var with (psi0 := psi0); eauto.  transitivity psi; auto.
  - (* pi *)
    fresh_apply_Typing x; auto.
    repeat spec x.
    match goal with [H4 : forall psi2, ?psi <= psi2 -> _ |- _ ] => 
    specialize (H4 psi2 ltac:(auto));
    apply Typing_pumping with (psi1:=psi2) in H4; try reflexivity end.
    eapply Typing_narrowing; eauto.
    econstructor; eauto using ctx_sub_refl, Typing_uniq.
    eapply leq_join_r.
    auto.
  - (* abs *)
    fresh_apply_Typing x; eauto.
    repeat spec x.
    match goal with [H4 : forall psi2, ?psi <= psi2 -> _ |- _ ] => 
    specialize (H4 psi2 ltac:(auto));
    apply Typing_pumping with (psi1:=psi2) in H4; try reflexivity;
    rewrite <- join_assoc in H4;
    rewrite (join_leq psi psi2) in H4; eauto end.
  - (* app *)
    eapply T_App; eauto.
    eapply IHTyping2; eauto.
    eauto using po_join_r.
  - (* wsigma *)
    fresh_apply_Typing x; eauto.
    repeat spec x.
    match goal with [H5 : forall psi2, ?psi <= psi2 -> _ |- _ ] => 
    specialize (H5 psi2 ltac:(auto));
    apply Typing_pumping with (psi1:=psi2) in H5; try reflexivity end.
    eapply Typing_narrowing; eauto.
    econstructor; eauto using ctx_sub_refl, Typing_uniq.
    eapply leq_join_r.
  - (* wpair *)
    eapply T_WPair; eauto.
    eapply IHTyping2; eauto.
    eauto using po_join_r.
  - (* letpair *)
    admit.
    (* fresh_apply_Typing x; eauto.
    move=> y FrY.
    clear H H0 H2.
    spec x. spec y.
    specialize (H0 psi2 ltac:(auto) ltac:(auto)).
    apply Typing_pumping with (psi1:=psi2) in H0; try reflexivity.
    rewrite <- join_assoc in H0.
    rewrite (join_leq psi psi2) in H0. auto.
    auto. *)
  - (* SSigma *)
    fresh_apply_Typing x; eauto.
    repeat spec x.
    match goal with [H5 : forall psi2, ?psi <= psi2 -> _ |- _ ] => 
    specialize (H5 psi2 ltac:(auto));
    apply Typing_pumping with (psi1:=psi2) in H5; try reflexivity end.
    eapply Typing_narrowing; eauto.
    econstructor; eauto using ctx_sub_refl, Typing_uniq.
    eapply leq_join_r.
  - (* SPair *)
    eapply T_SPair; eauto using po_join_r.
  - (* proj1 *)
    eapply T_Proj1; eauto. transitivity psi; auto.
  - (* case *)
    fresh_apply_Typing x; eauto.
    transitivity psi; auto.
Admitted.

(*
Lemma Typing_lift : forall W psi a A, Typing W psi a A -> Typing (meet_ctx_l q_C W) q_C a A.
Proof.
  intros.
  eapply Typing_subsumption with (psi1 := psi); eauto.
  eapply Typing_narrowing; eauto.
  eapply meet_ctx_l_ctx_sub.
  eapply Typing_uniq. eauto.
  eapply Typing_leq_C; eauto.
  reflexivity.
Qed.
*)


(* 
   The difficult case of this lemma is when ~ psi <= q_C. 
   We need to go from a "squashed judgement" at q_C to one that is squashed down to q_C + psi. 
   If psi >= q_C then we are done. But if not, then the meet will be lower than q_C and we don't 
   want that.
 *)
(*
Lemma meet_ctx_l_CTyping : forall W psi a A, CTyping W psi a A -> CTyping (meet_ctx_l q_C W) (q_C + psi) a A.
Proof.
  intros. inversion H. subst.
  + have L: psi <= q_C. eapply Typing_leq_C; eauto.
    rewrite meet_comm.
    eapply CT_Leq; eauto.
    rewrite meet_leq. auto.
    eapply Typing_meet_ctx_l. auto. eapply leq_meet_r.
  + subst.
    have h1: (q_C + psi <= q_C). eapply leq_meet_l.
    eapply CT_Leq; eauto.
    inversion H1. rewrite meet_leq; auto.
Qed. *)


Lemma Ctx_meet_ctx_l : forall W, Ctx W -> Ctx (meet_ctx_l q_C W).
Proof. 
  induction 1; simpl; simpl_env; eauto.
  econstructor; simpl_env; eauto.
  rewrite dom_meet_ctx_l. auto.
Qed.  

Lemma Ctx_regularity : forall G x psi A, Ctx G -> binds x (psi, A) G 
                                    -> exists s, Typing (meet_ctx_l q_C G) q_C A (a_Type s).
Proof.
  induction 1; intros; eauto. inversion H.
  simpl in H2.
  destruct (binds_cons_1 _ _ _ _ _ _ H2).
  + split_hyp. inversion H4. subst.
    simpl_env. eexists.
    eapply Typing_weakening; eauto.
    unfold meet_ctx_l; auto.
    move: (Typing_uniq H0) => u. unfold meet_ctx_l in u. 
    simpl. solve_uniq.
  + simpl_env.
    destruct IHCtx as [s0 T]; auto.
    eexists.
    eapply Typing_weakening; eauto.
    unfold meet_ctx_l; auto.
    move: (Typing_uniq H0) => u. unfold meet_ctx_l in u. 
    simpl. solve_uniq.
Qed.


Ltac subst_CTyping_ih :=
    match goal with 
      [ H3 : forall x0 psi1 A1 W3 W4, [(?y, (?q, ?A0))] ++ ?W2 ++ [(?x, (?psi0, ?A))] ++ ?W1 ~= _ -> _ |- _ ] => 
      specialize (H3 x psi0 A W1 ([(y, (q, A0))] ++ W2)) ; simpl_env in H3 ; 
      specialize (H3 ltac:(reflexivity) ltac:(eassumption)) ;
      unfold subst_ctx in H3; simpl_env in H3 ; specialize (H3 ltac:(solve_uniq));
        repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto using CTyping_lc1, CTyping_lc2;
          rewrite subst_tm_tm_var_neq in H3; auto end.

Lemma Typing_substitution_Typing : forall x psi0 A W1 W2 psi b a B, 
    Typing (W2 ++ [(x, (psi0, A))] ++ W1) psi b B ->
    Ctx W1 ->
    Typing W1 psi0 a A -> 
    Typing (subst_ctx a x W2 ++ W1) psi (subst_tm_tm a x b) (subst_tm_tm a x B).
Proof.
  intros.
  have uu: uniq (subst_ctx a x W2 ++ W1) by
    move: (Typing_uniq H) => u1; unfold subst_ctx; solve_uniq.
  dependent induction H.
  all: simpl; eauto 2.
  - (* conv *)
    simpl_env in *. 
    eapply T_Conv with (psi:=psi); simpl_env; eauto 3.
    eapply DefEq_substitution_CGrade; eauto 1.
    destruct (order_q_C_dec psi0) eqn:LE.
    + rewrite meet_comm.
      rewrite meet_leq. auto.
      eapply CG_Leq; auto.
      eapply Typing_Grade.
      eapply Typing_subsumption; eauto.
      eapply Typing_narrowing; eauto. 
      eapply meet_ctx_l_ctx_sub.
      eapply Typing_uniq; eauto.
    + match goal with [ H4 : q_C < ?psi0 |- _ ] => inversion H4 end. 
      rewrite meet_leq in H0; auto.
      eapply DefEq_substitution_same; eauto.
      eapply Typing_Grade.
      eapply Typing_subsumption; eauto. reflexivity. 
    -- eapply IHTyping2;
       eauto using Ctx_meet_ctx_l.
  - (* var *)
    destruct (x0 == x) eqn:E.
    match goal with [ H3 : CTyping _ _ _ _ |- _ ] => inversion H3; subst; clear H3 end.
    + (* substituting for this variable, relevant. *)
      apply binds_mid_eq in H1; auto. inversion H1. subst. clear H1.
      destruct_uniq.
      rewrite subst_tm_tm_fresh_eq; eauto.
      move: (Typing_ctx_fv ltac:(eassumption) ltac:(eassumption)) => [h1 h2]. fsetdec.
      eapply Typing_weakening_middle with (W2 := nil); simpl_env; eauto.
      eapply Typing_subsumption; eauto.
    + (* this variable, but irrelevant. contradiction *)
      apply binds_mid_eq in H1; auto. inversion H1. subst. clear H1.
      move: (lt_not_leq H5) => LE.
      have L: psi0 <= q_C by transitivity psi; auto.
      done.
    + eapply T_Var; eauto.
      apply binds_remove_mid in H1; auto.
      destruct (binds_app_1 _ _ _ _ _ H1).
      ++ eapply binds_map with (f := fun '(q, A) => (q, subst_tm_tm a x A)) in H5.
         eapply binds_app_2. auto.
      ++ eapply binds_app_3.   
         rewrite subst_tm_tm_fresh_eq; eauto.
         move: (Ctx_regularity _ _ _ ltac:(eassumption) H5) => [s0 h1].
         move: (Typing_ctx_fv h1 (Ctx_meet_ctx_l H3)) => [h2 h3].
         destruct_uniq.
         rewrite dom_meet_ctx_l in h2.
         fsetdec.
  - (* pi *)
    fresh_apply_Typing y; eauto.
    eapply IHTyping; eauto.
    repeat spec y.
    subst_CTyping_ih.
  - (* abs *)
    fresh_apply_Typing y.  repeat spec y.
    subst_CTyping_ih.
    simpl_env. eapply IHTyping; simpl_env; eauto.
    eauto using Ctx_meet_ctx_l.
    eapply meet_ctx_l_CTyping; eauto.
    move: (Typing_uniq H1) => u.
    unfold subst_ctx. simpl_env in u. solve_uniq.
  - (* App *)
    rewrite subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.
    eapply T_App; eauto.
    eapply IHTyping1; eauto.
  - (* AppI *)
    rewrite subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.
    simpl_env in H0. 
    eapply T_AppIrrel; eauto.
    eapply IHTyping1; eauto.
    fold subst_tm_tm.
    simpl_env.
    eapply IHTyping2; eauto using Ctx_meet_ctx_l. simpl_env. eauto.
    + eapply meet_ctx_l_CTyping; eauto.
    + move: (Typing_uniq H0) => u. destruct_uniq.
      unfold subst_ctx in *.
      eapply uniq_app; eauto.
  - (* WSigma *)
    fresh_apply_Typing y; eauto.
    eapply IHTyping; eauto.
    repeat spec y.
    subst_CTyping_ih.
  - (* WPair *)
    eapply T_WPair; eauto.
    + specialize (IHTyping1 x (q_C + psi0) A (meet_ctx_l q_C W1) (meet_ctx_l q_C W2)).
      simpl in IHTyping1.
      simpl_env in IHTyping1.
      simpl_env. eapply IHTyping1; eauto using meet_ctx_l_CTyping, Ctx_meet_ctx_l.
      move: (Typing_uniq H) => u. simpl_env in u. unfold subst_ctx. solve_uniq.
    + specialize (IHTyping3 x psi0 A W1 W2 ltac:(auto)).
      rewrite subst_tm_tm_open_tm_wrt_tm in IHTyping3; eauto using CTyping_lc1.
  - (* WPairI *)
    eapply T_WPairIrrel; simpl_env; eauto.
    + specialize (IHTyping1 x (q_C + psi0) A (meet_ctx_l q_C W1) (meet_ctx_l q_C W2)).
      simpl in IHTyping1.
      simpl_env in IHTyping1.
      simpl_env. eapply IHTyping1; eauto using meet_ctx_l_CTyping, Ctx_meet_ctx_l.
      move: (Typing_uniq H) => u. simpl_env in u. unfold subst_ctx. solve_uniq.
    + specialize (IHTyping2 x (q_C + psi0) A (meet_ctx_l q_C W1) (meet_ctx_l q_C W2)).
      simpl in IHTyping2.
      simpl_env in IHTyping2.
      simpl_env. eapply IHTyping2; eauto using meet_ctx_l_CTyping, Ctx_meet_ctx_l.
      move: (Typing_uniq H) => u. simpl_env in u. unfold subst_ctx. solve_uniq.
    + specialize (IHTyping3 x psi0 A W1 W2 ltac:(auto)).
      rewrite subst_tm_tm_open_tm_wrt_tm in IHTyping3; eauto using CTyping_lc1.
  - (* LetPair *)
    rewrite subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.
    move: (Typing_uniq H1) => u.
    fresh_apply_Typing y. 
    + clear H H2 H3. spec y.
      specialize (H x (q_C + psi0) A (meet_ctx_l q_C W1) ([(y, (q_C, a_WSigma psi1 A0 B))] ++ meet_ctx_l q_C W2)).
      simpl in H. simpl_env in H.
      specialize (H ltac:(eauto) ltac:(eauto using Ctx_meet_ctx_l) ltac:(eauto using meet_ctx_l_CTyping)).
      rewrite subst_tm_tm_open_tm_wrt_tm in H; eauto using CTyping_lc1.
      rewrite subst_tm_tm_var_neq in H; eauto. 
      simpl_env. eapply H.
      eapply uniq_cons_3; eauto.
      unfold subst_ctx. unfold meet_ctx_l.
      solve_uniq.
      unfold subst_ctx. unfold meet_ctx_l.
      auto.
    + eapply IHTyping; eauto.
    + clear H H0 H2 IHTyping.
      move=> z Frz.
      spec y. spec z.
      specialize (H0 x psi0 A W1 ([(y, (psi1 * psi, A0))] ++ W2)).
      simpl_env in H0.
      specialize (H0 ltac:(reflexivity) ltac:(eassumption) ltac:(auto)).
      simpl in H0. simpl_env in H0.
      repeat rewrite subst_tm_tm_open_tm_wrt_tm in H0; eauto using CTyping_lc1.
      rewrite subst_tm_tm_var_neq in H0. auto.
      repeat rewrite subst_tm_tm_close_tm_wrt_tm in H0; eauto using CTyping_lc1.
      repeat rewrite subst_tm_tm_open_tm_wrt_tm in H0; eauto using CTyping_lc1.
      simpl in H0.
      destruct (y == x) eqn:E. subst. clear Frz. fsetdec. rewrite E in H0.
      destruct (z == x) eqn:E2. subst. clear Fr. fsetdec. rewrite E2 in H0.
      simpl_env in H0.
      eapply H0.
      unfold subst_ctx.
      solve_uniq.
  - (* SSigma *)
    fresh_apply_Typing y; eauto. 
    eapply IHTyping; eauto.
    repeat spec y.
    subst_CTyping_ih.
  - (* SPair *)
    eapply T_SPair; eauto.
    + specialize (IHTyping1 x (q_C + psi0) A (meet_ctx_l q_C W1) (meet_ctx_l q_C W2)).
      simpl in IHTyping1.
      simpl_env in IHTyping1.
      simpl_env. eapply IHTyping1; eauto using meet_ctx_l_CTyping, Ctx_meet_ctx_l.
      move: (Typing_uniq H) => u. simpl_env in u. unfold subst_ctx. solve_uniq.
    + specialize (IHTyping3 x psi0 A W1 W2 ltac:(auto)).
      rewrite subst_tm_tm_open_tm_wrt_tm in IHTyping3; eauto using CTyping_lc1.
  - (* Proj1 *)
    eapply T_Proj1; eauto.
    simpl in IHTyping; eauto.
  - (* Proj2 *)
    rewrite subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.    
    eapply T_Proj2; eauto. fold subst_tm_tm.
    simpl in IHTyping; eauto.
  - (* Sum *)
    eauto.
  - (* Inj1 *)
    eapply T_Inj1; eauto.
    specialize (IHTyping2 x (q_C + psi0) A (meet_ctx_l q_C W1) (meet_ctx_l q_C W2)).
    simpl in IHTyping2.
    simpl_env in IHTyping2.
    simpl_env. eapply IHTyping2; eauto using meet_ctx_l_CTyping, Ctx_meet_ctx_l.
    move: (Typing_uniq H0) => u. simpl_env in u. unfold subst_ctx. solve_uniq.
  - (* Inj2 *)
    eapply T_Inj2; eauto.
    specialize (IHTyping2 x (q_C + psi0) A (meet_ctx_l q_C W1) (meet_ctx_l q_C W2)).
    simpl in IHTyping2.
    simpl_env in IHTyping2.
    simpl_env. eapply IHTyping2; eauto using meet_ctx_l_CTyping, Ctx_meet_ctx_l.
    move: (Typing_uniq H0) => u. simpl_env in u. unfold subst_ctx. solve_uniq.
  - (* case *)
    have US:  uniq (subst_ctx a x (meet_ctx_l q_C W2) ++ meet_ctx_l q_C W1).
    { eapply uniq_map_app_l.
      rewrite <- meet_ctx_l_app.
      eapply uniq_map_2.
      unfold subst_ctx in uu. solve_uniq.
      }
    have LCa: lc_tm a. eauto using CTyping_lc1.
    rewrite subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.    
    pick fresh y and apply T_Case; auto. 
    3: { instantiate (1 := subst_tm_tm a x B1). 
         replace (a_Var_f y) with (subst_tm_tm a x (a_Var_f y)).
         rewrite <- subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.    
         rewrite H2. eauto.
         rewrite -> subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.    
         rewrite subst_tm_tm_var_neq; auto.
    } 
    3: { instantiate (1 := subst_tm_tm a x B2). 
         replace (a_Var_f y) with (subst_tm_tm a x (a_Var_f y)).
         rewrite <- subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.    
         rewrite H3. eauto.
         rewrite -> subst_tm_tm_open_tm_wrt_tm; eauto using CTyping_lc1.    
         rewrite subst_tm_tm_var_neq; auto.
    } 

    + simpl_env.
      repeat spec y.
      specialize (H2 x (q_C + psi0) A (meet_ctx_l q_C W1) ([(y, (q_C, a_Sum A1 A2))] ++ (meet_ctx_l q_C W2))).
      simpl_env in H2.
      specialize (H2 ltac:(auto) ltac:(eauto using Ctx_meet_ctx_l) ltac:(eauto using meet_ctx_l_CTyping)).
      rewrite subst_tm_tm_open_tm_wrt_tm in H2; eauto using CTyping_lc1.    
      rewrite subst_tm_tm_var_neq in H2. auto.
      simpl in H2. simpl_env in H2.
      eapply H2.
      eapply uniq_cons_3. auto.
      repeat rewrite dom_app. unfold subst_ctx. rewrite dom_map. repeat rewrite dom_meet_ctx_l. eauto.
    + eapply IHTyping1; eauto.
    + eapply IHTyping2; eauto.
    + eapply IHTyping3; eauto.
Qed. 



Lemma Typing_substitution_middle : forall x psi0 A W1 W2 psi b a B, 
    Typing (W2 ++ [(x, (psi0, A))] ++ W1) psi b B ->
    Typing W1 psi0 a A -> Ctx W1 ->
    Typing (subst_ctx a x W2 ++ W1) psi (subst_tm_tm a x b) (subst_tm_tm a x B).
Proof.
  intros.
  have LT: (psi0 <= q_C) by eauto using Typing_leq_C.
  eapply Typing_substitution_CTyping; eauto.
Qed.


Lemma Typing_substitution_irrel : forall x psi0 psi A W1 W2 b a B, 
    Typing (W2 ++ [(x, (psi0, A))] ++ W1) psi b B ->
    q_C < psi0 ->
    Typing (meet_ctx_l q_C W1) q_C a A -> Ctx W1 ->
    Typing (subst_ctx a x W2 ++ W1) psi (subst_tm_tm a x b) (subst_tm_tm a x B).
Proof.
  intros.
  eapply Typing_substitution_CTyping; eauto.
Qed.


Lemma Typing_substitution : forall x psi0 A W psi b a B, 
    Typing ([(x, (psi0, A))] ++ W) psi b B ->
    Typing W psi0 a A ->  Ctx W ->
    Typing W psi (subst_tm_tm a x b) (subst_tm_tm a x B).
intros. eapply Typing_substitution_middle with (W2 := nil); eauto. Qed.

Lemma Typing_open : forall x psi0 A W psi b a B, 
    x `notin` fv_tm_tm b \u fv_tm_tm B ->
    Typing ([(x, (psi0, A))] ++ W) psi (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) ->
    Typing W psi0 a A -> Ctx W ->
    Typing W psi (open_tm_wrt_tm b a) (open_tm_wrt_tm B a).
Proof.
  intros. 
  rewrite (subst_tm_tm_intro x b); auto.
  rewrite (subst_tm_tm_intro x B); auto.
  eapply Typing_substitution; eauto.
Qed.



Local Lemma CTyping_Var : forall y psi0 A W, y `notin` dom W -> uniq W -> CTyping ([(y, (psi0, A))] ++ W) psi0 (a_Var_f y) A.
Proof. 
  intros.
  destruct (order_q_C_dec psi0).
  eapply CT_Leq; eauto.
  eapply T_Var; eauto using q_leb_refl.
  eapply CT_Top; eauto; simpl_env.
  eapply T_Var; unfold meet_ctx_l; eauto using q_leb_refl.
  inversion q.
  rewrite meet_leq; auto.
Qed.

Lemma Typing_rename : forall x y W psi0 A psi b B, 
   x `notin` fv_tm_tm b \u fv_tm_tm B  ->
   y `notin` fv_tm_tm b \u fv_tm_tm B \u dom W \u {{x}} ->
   Typing ([(x, (psi0, A))] ++ W) psi (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) ->
   Ctx ([(y, (psi0, A))] ++ W) -> 
   Typing ([(y, (psi0, A))] ++ W) psi (open_tm_wrt_tm b (a_Var_f y)) (open_tm_wrt_tm B (a_Var_f y)).
Proof.
  intros.
  move: (Typing_uniq H1) => u. destruct_uniq.
  apply Typing_weakening_middle with (W := [(y,(psi0,A))]) in H1.
  rewrite (subst_tm_tm_intro x b); auto.
  rewrite (subst_tm_tm_intro x B); auto.
  eapply Typing_substitution_CTyping with (W2 := nil); simpl_env; eauto.
  eapply CTyping_Var; eauto.
  solve_uniq.
Qed.


Lemma Typing_rename_Type : forall x y W psi0 A psi b s, 
   x `notin` fv_tm_tm b  ->
   y `notin` fv_tm_tm b \u dom W \u {{x}} ->
   Typing ([(x, (psi0, A))] ++ W) psi (open_tm_wrt_tm b (a_Var_f x)) (a_Type s)->
   Ctx ([(y, (psi0, A))] ++ W) -> 
   Typing ([(y, (psi0, A))] ++ W) psi (open_tm_wrt_tm b (a_Var_f y)) (a_Type s).
Proof.
  intros.
  move: (Typing_uniq H1) => u. destruct_uniq.
  apply Typing_weakening_middle with (W := [(y,(psi0,A))]) in H1.
  rewrite (subst_tm_tm_intro x b); auto.
  replace (a_Type s) with (subst_tm_tm (a_Var_f y) x (a_Type s)).
  eapply Typing_substitution_CTyping with (W2 := nil); simpl_env; eauto.
  eapply CTyping_Var; eauto.
  reflexivity.
  solve_uniq.
Qed.

Lemma T_Pi_inversion: forall (x : atom) W (psi psi1 : grade) (A B C : tm),
    x `notin` dom W \u fv_tm_tm B ->
    Typing W psi (a_Pi psi1 A B) C ->
    Ctx W -> 
    exists s1, exists s2, exists s3, rule s1 s2 s3 /\
  Typing W psi A (a_Type s1) /\ 
  Typing ([(x, (psi, A))] ++ W) psi (open_tm_wrt_tm B (a_Var_f x)) (a_Type s2) /\
  DefEq (labels (meet_ctx_l q_C W)) q_C  C (a_Type s3).
Proof. 
  intros.
  dependent induction H0.  
  - (* conv *) 
    edestruct IHTyping1 as [s1 [s2 [s3 [r [hA [psi0 hh]]]]]]; eauto.
    repeat eexists; eauto.
  - (* Pi *) 
    pick fresh y.
    repeat spec y.  clear IHTyping. 
    eapply (@Typing_rename_Type y) in H1; eauto.
    repeat eexists.    
    eauto. eauto. eauto.
    eapply Eq_Refl; eauto.
    econstructor.
    apply labels_uniq. move: (Typing_uniq H0) => u. unfold meet_ctx_l. auto.
    econstructor; eauto using Typing_lift.    
Qed.

(* This is from Misha-Linger's thesis. I don't know if we need it. *)
(*
Lemma Sq_Pi_inversion: forall (x : atom) W (psi psi1 : grade) (A B C : tm),
    x `notin` dom W \u fv_tm_tm B ->
    q_C < psi ->
    CTyping W psi (a_Pi psi1 A B) C ->
    Ctx W ->
    CTyping W psi A a_Type /\ 
            CTyping ([(x, (psi1, A))] ++ W) psi (open_tm_wrt_tm B (a_Var_f x)) a_Type /\
            DefEq (labels (meet_ctx_l q_C W)) q_C  C a_Type.
Proof. 
  intros.
  inversion H1. subst. 
  + move: (Typing_leq_C H3) => LE.
    inversion H0. apply q_leb_antisym in LE; auto. done.
  + subst.
    eapply T_Pi_inversion with (x:= x) in H3; eauto. split_hyp.
    move: (Typing_uniq H5) => u. destruct_uniq.
    repeat split.
    eapply CT_Top; eauto.
    eapply CT_Top; eauto.
    simpl_env.
    eapply Typing_narrowing; eauto.
    econstructor; eauto using ctx_sub_refl, Typing_uniq.
    eapply leq_meet_l.
    simpl_env in *. auto.
    unfold meet_ctx_l. auto.
    eauto using Ctx_meet_ctx_l.
Qed.
*)

Lemma T_SSigma_inversion: forall (x : atom) W (psi psi1 : grade) (A B C : tm),
    x `notin` dom W \u fv_tm_tm B ->
    Typing W psi (a_SSigma psi1 A B) C ->
    Ctx W ->
     exists s1, exists s2, exists s3, rule s1 s2 s3 /\
    Typing W psi A (a_Type s1) /\ 
    Typing ([(x, (psi, A))] ++ W) psi (open_tm_wrt_tm B (a_Var_f x)) (a_Type s2) /\
    DefEq (labels (meet_ctx_l q_C W)) q_C C (a_Type s3).
Proof.
  intros.
  dependent induction H0.  
  - (* conv *) 
    edestruct IHTyping1 as [s1 [s2 [s3 [r [hA [psi0 hh]]]]]]; split_hyp; eauto.
    repeat eexists; eauto.
  - (* Pi *) 
    pick fresh y.
    repeat spec y.  clear IHTyping. 
    eapply (@Typing_rename_Type y) in H1; eauto.
    repeat eexists.    
    eauto. eauto. eauto.
    eapply Eq_Refl; eauto.
    econstructor.
    apply labels_uniq. move: (Typing_uniq H0) => u. unfold meet_ctx_l. auto.
    econstructor; eauto using Typing_lift.
Qed.


Lemma T_WSigma_inversion: forall (x : atom) W (psi psi1 : grade) (A B C : tm),
   x `notin` dom W \u fv_tm_tm B ->
   Typing W psi (a_WSigma psi1 A B) C ->
   Ctx W ->
   exists s1, exists s2, exists s3, rule s1 s2 s3 /\
   Typing W psi A (a_Type s1) /\ 
   Typing ([(x, (psi, A))] ++ W) psi (open_tm_wrt_tm B (a_Var_f x)) (a_Type s2) /\
   DefEq (labels (meet_ctx_l q_C W)) q_C C (a_Type s3).
Proof.
  intros.
  dependent induction H0.  
  - (* conv *) 
    edestruct IHTyping1 as [s1 [s2 [s3 [r [hA [psi0 hh]]]]]]; split_hyp; eauto.
    repeat eexists; eauto.
  - (* Pi *) 
    pick fresh y.
    repeat spec y.  clear IHTyping. 
    eapply (@Typing_rename_Type y) in H1; eauto.
    repeat eexists. eauto. eauto. eauto.
    eapply Eq_Refl; eauto.
    econstructor.
    apply labels_uniq. move: (Typing_uniq H0) => u. unfold meet_ctx_l. auto.
    econstructor; eauto using Typing_lift.
Qed.


(* Coherence *)
Lemma Typing_regularity : 
  forall G psi a A, Typing G psi a A -> Ctx G -> exists s, Typing (meet_ctx_l q_C G) q_C A (a_Type s).
Proof. 
  induction 1; split_hyp; intros.
  all: try solve [eexists; eauto].
  all: try solve [ unfold meet_ctx_l; eauto using q_leb_refl ].
  - (* sort *) 
    destruct (sort_regularity s2).
    exists x. eapply T_Type; eauto. reflexivity. 
  - (* var *) eapply Ctx_regularity; eauto.
  - (* pi *)
    destruct (IHTyping ltac:(assumption)).
    destruct (sort_regularity s3).
    exists x0. eapply T_Type; eauto using Typing_uniq. reflexivity.
  - (* app *)
    clear IHTyping2. clear H.
    destruct IHTyping1 as [s h]; auto.
    pick fresh x.
    have Fr2: x `notin` dom (meet_ctx_l q_C W). unfold meet_ctx_l; eauto.
    move: (@T_Pi_inversion x (meet_ctx_l q_C W) q_C psi0 A B (a_Type s) ltac:(auto) ltac:(eauto) ltac:(eauto using Ctx_meet_ctx_l)) => [s1 [s2 [s3 [r hh]]]].
    exists s2.
    split_hyp.
    rewrite (subst_tm_tm_intro x); eauto.
    replace (a_Type s2) with (subst_tm_tm a x (a_Type s2)).
    eapply Typing_substitution; eauto 3.
    eapply Typing_meet_ctx_l; eauto.
    eapply Typing_subsumption; eauto.
    eapply Typing_leq_C; eauto. 
    reflexivity.
    eauto using Ctx_meet_ctx_l.
    auto.
  - (* AppI *)
    clear IHTyping2. clear H.
    destruct IHTyping1 as [s h]; auto.

    pick fresh x.
    have Fr2: x `notin` dom (meet_ctx_l q_C W). unfold meet_ctx_l; eauto.
    move: (@T_Pi_inversion x (meet_ctx_l q_C W) q_C psi0 A B (a_Type s) ltac:(auto) ltac:(eauto)  ltac:(eauto using Ctx_meet_ctx_l)) => [s1 [s2 [s3 [r hh]]]].
    exists s2.
    split_hyp.
    rewrite (subst_tm_tm_intro x); auto.
    replace (a_Type s2) with (subst_tm_tm a x (a_Type s2)).
    eapply Typing_substitution; eauto.
    eauto using Ctx_meet_ctx_l.
    auto.
  - (* ... *)
    destruct (sort_regularity s3).
    exists x. eapply T_Type; eauto using Typing_uniq. reflexivity. 
  - (* LetPair *)
    pick fresh x.
    repeat spec x.
    pick fresh y.
    repeat spec y.
    rewrite (subst_tm_tm_intro x); auto.
    clear H2. clear H3.
    destruct (IHTyping ltac:(assumption)) as [s1 hh].
    exists s.
    replace (a_Type s) with (subst_tm_tm a x (a_Type s)).
    eapply Typing_substitution; eauto 3.
    eapply Typing_meet_ctx_l; eauto.
    eapply Typing_subsumption; eauto.
    eapply Typing_leq_C; eauto. 
    reflexivity.
    eauto using Ctx_meet_ctx_l.
    auto.
  - (* sigma *)
    destruct (IHTyping ltac:(assumption)).
    destruct (sort_regularity s3).
    exists x0. eapply T_Type; eauto using Typing_uniq. reflexivity.
  - (* Proj1 *)
    pick fresh x.
    specialize (IHTyping ltac:(eauto)).
    destruct IHTyping as [s hT].
    have Fr2: x `notin` dom (meet_ctx_l q_C W). unfold meet_ctx_l; eauto.
    move: (@T_SSigma_inversion x (meet_ctx_l q_C W) q_C psi0 A B (a_Type s) ltac:(auto) ltac:(eauto)  ltac:(eauto using Ctx_meet_ctx_l)) => [s1 [s2 [s3 [r [h [psi1 hh]]]]]].
    split_hyp.
    eauto.
  - (* Proj2 *)
    pick fresh x.
    have Fr2: x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B. unfold meet_ctx_l; eauto.
    destruct IHTyping as [s hT]; auto.
    move: (@T_SSigma_inversion x _ _ psi0 A B (a_Type s) ltac:(auto) ltac:(eauto)  ltac:(eauto using Ctx_meet_ctx_l)) => [s1 [s2 [s3 [r [h [psi1 hh]]]]]].
    split_hyp.
    rewrite (subst_tm_tm_intro x); auto.
    exists s2.
    replace (a_Type s2) with (subst_tm_tm (a_Proj1 psi0 a) x (a_Type s2)).
    eapply Typing_substitution; eauto 1.
    eapply T_Proj1; eauto.
    eapply Typing_meet_ctx_l; eauto.
    eapply Typing_subsumption; eauto.
    eapply Typing_leq_C; eauto. reflexivity.
    eauto using Ctx_meet_ctx_l.
    auto.
  - (* case *)
    pick fresh x. exists s. 
    repeat spec x.
    rewrite (subst_tm_tm_intro x); auto.
    replace (a_Type s) with (subst_tm_tm a x (a_Type s)).
    eapply Typing_substitution; eauto 3.
    eapply Typing_meet_ctx_l; eauto.
    eapply Typing_subsumption; eauto.
    eapply Typing_leq_C; eauto. 
    reflexivity.
    eauto using Ctx_meet_ctx_l.
    auto.
  -  destruct (sort_regularity s).
    exists x. eapply T_Type; eauto using Typing_uniq. reflexivity.
Unshelve. exact star.
Qed.

Lemma T_App_inversion: forall W (psi psi0 : grade) (a b C : tm),
    Typing W psi (a_App b psi0 a) C -> Ctx W ->
    exists A B, Typing W psi b (a_Pi psi0 A B) /\ 
           CTyping W (psi0 * psi) a A /\
           DefEq (labels (meet_ctx_l q_C W)) q_C C (open_tm_wrt_tm B a).
Proof. 
  intros.
  dependent induction H.
  + (* conv *)
    edestruct IHTyping1 as [A1 [B1 hh]]; auto; try reflexivity.
    split_hyp.
    exists A1. exists B1.
    split; eauto.
  + (* app *)
    clear IHTyping1. clear IHTyping2.
    exists A. exists B.
    have LT: (psi0 * psi) <= q_C. eauto using Typing_leq_C.
    repeat split; auto.
    move: (Typing_regularity H ltac:(auto)) => [s0 hh].
    eapply Eq_Refl.
    move: (Typing_Grade hh) => gh.
    inversion gh. subst. 
    pick fresh y. rewrite (subst_tm_tm_intro y); eauto. repeat spec y.
    eapply Grade_substitution_same with (P2:=nil); eauto.
    eapply Typing_Grade. 
    eapply Typing_narrowing; eauto.
    eapply Typing_subsumption; eauto.
    eapply Typing_leq_C; eauto.
    eapply meet_ctx_l_ctx_sub.
    eapply Typing_uniq; eauto.
  + exists A. exists B. 
    repeat split; auto.
    have: (q_C < psi0 * psi).
    { eapply still_higher; eauto using Typing_leq_C. } 
    eapply CT_Top; eauto.
    apply Typing_regularity in H.
    move: H => [s0 HH].
    pick fresh x.
    apply (@T_Pi_inversion x) in HH; auto.
    move: HH => [s1 [s2 [s3 [r TH]]]].
    split_hyp.
    eapply Eq_Refl; eauto.
    eapply Typing_Grade with (A := subst_tm_tm a x (a_Type s2)) ; eauto.
    rewrite (subst_tm_tm_intro x); auto.
    eapply Typing_substitution; eauto using Ctx_meet_ctx_l.
    unfold meet_ctx_l; eauto.
    eauto using Ctx_meet_ctx_l.
    auto.
Qed.


Lemma T_Abs_inversion: forall W (psi psi0 : grade) (b C A : tm),
    Typing W psi (a_Abs psi0 A b) C -> 
    Ctx W ->
    forall x, x `notin` dom W \u fv_tm_tm b ->
         exists s B, 
           Typing ([(x, (psi0 * psi, A))] ++ W) psi (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) /\
           (DefEq (labels (meet_ctx_l q_C W)) q_C C (a_Pi psi0 A B) /\ 
            Typing (meet_ctx_l q_C W) q_C (a_Pi psi0 A B) (a_Type s)) /\
            x `notin` fv_tm_tm B.
Proof. 
  intros.
  dependent induction H.
  + (* conv *)
    edestruct IHTyping1 as [s0 [B1 hh]]; auto; try reflexivity. 
    split_hyp.
    repeat eexists; eauto 2.
    eapply Eq_Trans with (b:=A0); auto.
  + (* abs *)
    clear IHTyping. 
    move: (Typing_ctx_fv H1 ltac:(eauto using Ctx_meet_ctx_l)) => [h0 _]. 
    simpl in h0. rewrite dom_meet_ctx_l in h0.
    pick fresh y. repeat spec y.
    have Fr1: y `notin` dom (meet_ctx_l q_C W). {     rewrite dom_meet_ctx_l. auto. }

    move: (@T_Pi_inversion y (meet_ctx_l q_C W) q_C psi0 A B (a_Type s) ltac:(auto) ltac:(eauto)  ltac:(eauto using Ctx_meet_ctx_l)) => [s1 [s2 [s3 [r [h [hh1 hh2]]]]]].    
    exists s. exists B.
    repeat split; eauto 3.
    eapply (@Typing_rename y); auto 2.
    fsetdec.
    econstructor; eauto.
    eapply Eq_Refl.
    eapply Typing_Grade.
    eauto.
    eauto.
    eauto using Ctx_meet_ctx_l.

    fsetdec.
Qed.



Lemma T_SPair_inversion : forall W psi a psi0 b C,
       Typing W psi (a_SPair a psi0 b) C ->
       exists s A B, Typing (meet_ctx_l q_C W) q_C (a_SSigma psi0 A B) (a_Type s) /\
              Typing W (psi0 * psi) a A /\
              Typing W psi b (open_tm_wrt_tm B a) /\
              DefEq (labels (meet_ctx_l q_C W)) q_C C (a_SSigma psi0 A B).
Proof.
  intros. 
  dependent induction H.
  - edestruct IHTyping1 as [s0 [A1 [B1 hh]]]; auto; try reflexivity. 
    split_hyp.
    repeat eexists; eauto. 
  - exists s. exists A. exists B.
    repeat split; eauto 1.
    eapply Eq_Refl; eauto.
    eapply Typing_Grade; eauto.
Qed.


Lemma T_WPair_inversion : forall W psi a psi0 b C,
       Typing W psi (a_WPair a psi0 b) C ->
       exists s A B, Typing (meet_ctx_l q_C W) q_C (a_WSigma psi0 A B) (a_Type s) /\
              CTyping W (psi0 * psi) a A /\
              Typing W psi b (open_tm_wrt_tm B a) /\
              DefEq (labels (meet_ctx_l q_C W)) q_C C (a_WSigma psi0 A B).
Proof.
  intros. 
  dependent induction H.
  - edestruct IHTyping1 as [s0 [A1 [B1 hh]]]; auto; try reflexivity. 
    split_hyp.
    repeat eexists; eauto. 
  - exists s. exists A. exists B.
    have LT: (psi0 * psi <= q_C) by eauto using Typing_leq_C.
    repeat split; eauto 3.
    eapply Eq_Refl; eauto.
    eapply Typing_Grade; eauto.
  - exists s. exists A. exists B.
    repeat split; eauto 3.
    eapply CT_Top; eauto using still_higher, Typing_leq_C.
    eapply Eq_Refl; eauto.
    eapply Typing_Grade; eauto.
Qed.

Lemma T_Inj1_inversion : forall {W psi a0 C}, 
      Typing W psi (a_Inj1 a0) C -> Ctx W ->
      exists A1 A2, DefEq (labels (meet_ctx_l q_C W)) q_C (a_Sum A1 A2) C /\
               Typing W psi a0 A1.
Proof.
      intros. dependent induction H.
      - edestruct IHTyping1 as [A1 [A2 hh]]; eauto.
        exists A1. exists A2. split_hyp. split.
        eapply Eq_Trans with (b := A); auto using Eq_Sym.
        auto.
      - exists A1. exists A2. split.
        move: (Typing_regularity H ltac:(auto)) => hh.
        eapply Eq_Sym; eauto using Eq_Refl, Typing_Grade.
        auto.
Qed.

Lemma T_Inj2_inversion : forall {W psi a0 C}, 
      Typing W psi (a_Inj2 a0) C -> Ctx W ->
      exists A1 A2, DefEq (labels (meet_ctx_l q_C W)) q_C (a_Sum A1 A2) C /\
               Typing W psi a0 A2.
Proof.
      intros. dependent induction H.
      - edestruct IHTyping1 as [A1 [A2 hh]]; eauto.
        exists A1. exists A2. split_hyp. split.
        eapply Eq_Trans with (b := A); auto using Eq_Sym.
        auto.
      - exists A1. exists A2. split.
        move: (Typing_regularity H ltac:(auto)) => hh.
        eapply Eq_Sym; eauto using Eq_Refl, Typing_Grade.
        auto.
Qed.



Lemma Typing_preservation : forall W psi a A, Typing W psi a A -> Ctx W -> forall b, Step a b -> Typing W psi b A.
Proof.
  intros W psi a A h. induction h; intros;
                        match goal with [ H0 : Step ?a ?b |- _ ] => inversion H0; subst end.
  all: eauto.
  - (* Beta *)
    clear IHh1. clear IHh2.
    move: (T_Abs_inversion h1) => hh.
    pick fresh x.
    destruct (hh ltac:(auto) x ltac:(auto)) as [s [B0 hh1]]. split_hyp.
    have FrB0: x `notin` fv_tm_tm B0. eauto. clear hh.
    have FrW : x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B0. unfold meet_ctx_l. auto.
    move: (T_Pi_inversion FrW ltac:(eassumption) ltac:(eauto using Ctx_meet_ctx_l)) =>
    [s1 [s2 [s3 [r hh]]]]. split_hyp.
    have EA: DefEq (labels (meet_ctx_l q_C W)) q_C A A0.
      { 
        eapply Eq_PiFst; eauto.
      }
      have DO: DefEq (labels (meet_ctx_l q_C W)) q_C (open_tm_wrt_tm B a) (open_tm_wrt_tm B0 a).
      { 
        eapply Eq_PiSnd; eauto 2.
        eapply Typing_Grade; eauto.
        eapply Typing_subsumption with (psi1 := psi0 *psi); eauto.
        eapply Typing_narrowing; eauto.
        eapply meet_ctx_l_ctx_sub.
        eapply Typing_uniq.
        eauto.
        eapply Typing_leq_C.
        eauto.
        reflexivity.
      }
      move: (Typing_regularity h1 ltac:(auto)) => [s4 TAB].
      have FrW1 : x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B. unfold meet_ctx_l. auto.
      move: (T_Pi_inversion FrW1 TAB ltac:(eauto using Ctx_meet_ctx_l)) => 
         [s1' [s2' [s3' [r' hh]]]]. split_hyp.

      eapply Eq_Sym in DO.
      eapply T_Conv with (A := open_tm_wrt_tm B0 a) (s:= s2'); auto.      
      rewrite (subst_tm_tm_intro x _ a). eauto.
      rewrite (subst_tm_tm_intro x _ a). eauto.
      eapply Typing_substitution; eauto using Ctx_meet_ctx_l.
      rewrite (subst_tm_tm_intro x _ a). eauto.
      replace (a_Type s2') with (subst_tm_tm a x (a_Type s2')).
      eapply Typing_substitution; eauto using Ctx_meet_ctx_l.
   
      eapply Typing_subsumption with (psi1 := psi0 * psi); eauto.
      eapply Typing_narrowing; eauto.
      eapply meet_ctx_l_ctx_sub.
      eapply Typing_uniq; eauto.
      eapply Typing_leq_C; eauto.
      reflexivity.
      auto.
  - (* AppI *)
    move: (T_Abs_inversion h1 ltac:(auto)) => hh.
    pick fresh x.
    destruct (hh x ltac:(auto)) as [s0 [B0 hh1]]. split_hyp.
    have FrB0: x `notin` fv_tm_tm B0. auto. clear hh.
    have FrW : x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B0. unfold meet_ctx_l. auto.
    move: (T_Pi_inversion FrW ltac:(eassumption) ltac:(eauto using Ctx_meet_ctx_l)) =>  [s1 [s2 [s3 [r hh]]]]. split_hyp.
    have EA: DefEq (labels (meet_ctx_l q_C W)) q_C A A0.
      { 
        eapply Eq_PiFst; eauto.
      }
      have DO: DefEq (labels (meet_ctx_l q_C W)) q_C (open_tm_wrt_tm B a) (open_tm_wrt_tm B0 a).
      { 
        eapply Eq_PiSnd; eauto 2.
        eapply Typing_Grade; eauto.
      }
      move: (Typing_regularity h1 ltac:(auto)) => [s4 TAB].
      have FrW1 : x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B. unfold meet_ctx_l. auto.
      move: (T_Pi_inversion FrW1 TAB ltac:(eauto using Ctx_meet_ctx_l)) =>
      [s1' [s2' [s3' [r' hh']]]]. split_hyp.

      eapply Eq_Sym in DO.
      eapply T_Conv with (A := open_tm_wrt_tm B0 a)(s:=s2'); auto.
      rewrite (subst_tm_tm_intro x _ a). eauto.
      rewrite (subst_tm_tm_intro x _ a). eauto.
      eapply Typing_substitution_irrel with (W2 := nil); eauto using Ctx_meet_ctx_l. 
      eapply still_higher; eauto using Typing_leq_C.
      eapply T_Conv with (A := A); simpl_env; eauto. 

      rewrite (subst_tm_tm_intro x _ a). eauto.
      replace (a_Type s2') with (subst_tm_tm a x (a_Type s2')).
      eapply Typing_substitution; eauto using Ctx_meet_ctx_l.
      auto.

  - (* LetPair *)
    
    specialize (IHh ltac:(auto) ltac:(auto) ltac:(auto)).
    move: (Typing_lift h) => L1.
    move: (Typing_lift IHh) => L2'.
    have TCa: (Typing (meet_ctx_l q_C W) q_C (open_tm_wrt_tm C a) (a_Type s)).
    { 
      pick fresh x. repeat spec x.
      rewrite (subst_tm_tm_intro x _ a). eauto.
      replace (a_Type s) with (subst_tm_tm a x (a_Type s)). 2:auto.
      eapply Typing_substitution; eauto using Ctx_meet_ctx_l.
    } 
    have WE: DefEq (labels (meet_ctx_l q_C W)) q_C (a_SSigma psi0 A C) (a_SSigma psi0 A C).
      { eapply Eq_Refl.
        pick fresh x. move: (@T_WSigma_inversion x) => hh. 
        move: (Typing_regularity h ltac:(auto)) => [s' R].
        specialize (hh  (meet_ctx_l q_C W) q_C psi0 A B (a_Type s')).
        specialize (hh ltac:(rewrite dom_meet_ctx_l; eauto) R ltac:(eauto using Ctx_meet_ctx_l)).
        destruct hh as [s1 [s2 [s3 [r hh]]]].
        split_hyp.
        fresh_apply_Grade y. eapply Typing_Grade; eauto.
        specialize (H y ltac:(auto)).
        eapply Typing_Grade in H. simpl_env in H.
        eapply H.
      }
    have ECaa: DefEq (labels (meet_ctx_l q_C W)) q_C  (open_tm_wrt_tm C a')  (open_tm_wrt_tm C a).
      { eapply Eq_SSigmaSnd. eapply WE. eapply Eq_Sym. eapply Eq_Beta; eauto using Typing_Grade. }
    eapply T_Conv with (A := open_tm_wrt_tm C a'); try eauto 1.
    + pick fresh x and apply T_LetPair; eauto.

  - (* LetPair Beta1 *)
    clear H0. clear H2. clear IHh.
    pick fresh x. repeat spec x.
    pick fresh y. repeat spec y.
    move: (T_WPair_inversion h) => [s0 [A0 [B0 hh]]]. split_hyp.
    move: (Typing_regularity h ltac:(auto)) => [s' TWS].
    apply (@T_WSigma_inversion x) in TWS; try rewrite dom_meet_ctx_l; auto using Ctx_meet_ctx_l.
    destruct TWS as [s1 [s2 [s3 [r TWS]]]].
    split_hyp. 
    

    have Ta1 : CTyping W (psi0 * psi) a1 A.
    { 
      inversion H2; subst.
      eapply CT_Leq.
      eapply T_Conv; eauto 1.
      eapply Eq_WSigmaFst; eauto.
      auto.
      eapply CT_Top; eauto 1.
      eapply T_Conv; eauto 1.
      simpl_env.
      eapply Eq_WSigmaFst; eauto.
      simpl_env.  eauto.
    }

    have Ta2 : Typing W psi a2 (open_tm_wrt_tm B a1).
    { 
      eapply T_Conv. eassumption.
      eapply Eq_WSigmaSnd; eauto.
      eapply Typing_Grade; eauto.
      inversion H2; subst; eauto using Typing_lift.
      rewrite (subst_tm_tm_intro x); auto.
      replace (a_Type _) with (subst_tm_tm a1 x (a_Type s2)). 2: reflexivity.
      inversion H2; subst.
      + eapply Typing_substitution; eauto 3 using Ctx_meet_ctx_l.
        eapply Typing_lift.
        eapply T_Conv; eauto 1.
        eapply Eq_WSigmaFst; eauto.
      + eapply Typing_substitution; eauto 3 using Ctx_meet_ctx_l.
        eapply T_Conv; eauto 1.
        simpl_env.
        eapply Eq_WSigmaFst; eauto.
        simpl_env. eauto.
    }        

    have Tca1: Typing W psi (open_tm_wrt_tm c a1) 
                     (a_Pi q_Bot (open_tm_wrt_tm B a1) 
                          (close_tm_wrt_tm y (open_tm_wrt_tm C (a_WPair a1 psi0 (a_Var_f y))))).
    {
      rewrite (subst_tm_tm_intro x); auto.
      replace  (a_Pi q_Bot (open_tm_wrt_tm B a1) (close_tm_wrt_tm y (open_tm_wrt_tm C (a_WPair a1 psi0 (a_Var_f y)))))
         with 
        (subst_tm_tm a1 x (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f x))
                          (close_tm_wrt_tm y (open_tm_wrt_tm C (a_WPair (a_Var_f x) psi0 (a_Var_f y)))))).
      eapply Typing_substitution_CTyping with (W2 := nil); eauto 1.
      simpl.
      repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc1.
      rewrite subst_tm_tm_var.
      rewrite subst_tm_tm_fresh_eq; eauto.
      f_equal.
      repeat rewrite subst_tm_tm_close_tm_wrt_tm; eauto using Typing_lc1.
      repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc1.
      rewrite subst_tm_tm_fresh_eq; eauto.
      replace  (subst_tm_tm a1 x (a_WPair (a_Var_f x) psi0 (a_Var_f y))) with 
          (a_WPair (subst_tm_tm a1 x (a_Var_f x)) psi0 (subst_tm_tm a1 x (a_Var_f y))).
      rewrite subst_tm_tm_var.
      rewrite subst_tm_tm_var_neq. auto.
      auto.
      reflexivity.
    } 
    have Tb : Typing W psi (a_App (open_tm_wrt_tm c a1) q_Bot a2)
                     (open_tm_wrt_tm (close_tm_wrt_tm y (open_tm_wrt_tm C (a_WPair a1 psi0 (a_Var_f y)))) a2).
    { 
      eapply T_App; eauto 4 using leq_Bot.
      eapply Typing_subsumption. eassumption. eapply leq_join_r. 
      eapply join_lub; eauto using Typing_leq_C, leq_Bot.
    }
    rewrite <- subst_tm_tm_spec in Tb.
    rewrite subst_tm_tm_open_tm_wrt_tm in Tb. eauto using Typing_lc1. 
    rewrite subst_tm_tm_fresh_eq in Tb. auto.
    simpl in Tb. 
    rewrite subst_tm_tm_fresh_eq in Tb. auto.
    destruct (y == y) eqn:h1. rewrite h1 in Tb. auto. done.
  - (* Proj1 *)
    move: (T_SPair_inversion h) => [s0 [A0 [B0 hh]]]. split_hyp.
    move: (Eq_SSigmaFst _ _ _ _ _ _ _ ltac:(eassumption)) => h1.
    apply Typing_regularity in h; auto. destruct h as [s tS].
    pick fresh x.
    apply (@T_SSigma_inversion x) in tS. move: tS => [s1 [s2 [s3 [r hh]]]]. split_hyp.
    eapply T_Conv; eauto.
    rewrite join_leq in H3; auto.
    rewrite dom_meet_ctx_l. auto. eapply Ctx_meet_ctx_l; auto.

  - (* Proj2 Cong *)
    move: (Typing_regularity h ltac:(auto)) => [s0 TSS].
    pick fresh x. 
    have FrW: x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B.  unfold meet_ctx_l. auto.
    move: (T_SSigma_inversion FrW TSS ltac: (eauto using Ctx_meet_ctx_l)) => [s1 [s2 [s3 [r hh]]]]. split_hyp.

    have ES: DefEq (labels (meet_ctx_l q_C W)) q_C (a_SSigma psi0 A B) (a_SSigma psi0 A B).
    { eapply Eq_Refl. eapply Typing_Grade; eauto. } 

    have SE: DefEq (labels (meet_ctx_l q_C W)) q_C (a_Proj1 psi0 a) (a_Proj1 psi0 a'). 
    { eapply Eq_Beta; eauto.
      eapply Typing_Grade; eauto. 
      eapply T_Proj1; eauto.
      eapply Typing_lift; eauto.
      eapply Typing_Grade; eauto.
      eapply T_Proj1; eauto.
      eapply Typing_lift with (psi := psi); eauto.
    } 
    eapply T_Conv with (A := open_tm_wrt_tm B (a_Proj1 psi0 a')).
    eapply T_Proj2; eauto.
    eapply Eq_SSigmaSnd; eauto.

    match goal with 
      [ H2 : Typing ([(?x, (q_C, ?A))] ++ _) _ _ _ |- _ ] =>  
        eapply Typing_substitution with (a := a_Proj1 psi0 a) in H2;
        simpl in H2;
        try rewrite <- subst_tm_tm_intro in H2; eauto
        end.

    eapply T_Proj1; eauto.
    eapply Typing_lift; eauto.
    eauto using Ctx_meet_ctx_l.
  - (* Proj2 beta *)
    clear IHh.
    move: (T_SPair_inversion h) => [s0 [A0 [B0 hh]]]. split_hyp.
    subst.
    pick fresh x.
    have FrW : x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B0. unfold meet_ctx_l. auto.
    move: (T_SSigma_inversion FrW H2 ltac:(eauto using Ctx_meet_ctx_l)) => ?. split_hyp.
    move: (Typing_regularity h ltac:(auto)) => [s1 hh].
    have FrW1 : x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B. unfold meet_ctx_l. auto.
    move: (T_SSigma_inversion FrW1 hh ltac:(eauto using Ctx_meet_ctx_l)) => [s2 [s3 [s4 ?]]]. split_hyp.

    have TP : Typing (meet_ctx_l q_C W) q_C (a_Proj1 psi0 (a_SPair a1 psi0 b)) A0.
    {
      eapply T_Proj1; auto.
      eapply T_SPair; simpl_env; eauto.
      rewrite join_leq; auto.
      eapply Typing_lift; eauto.
      eapply Typing_lift; eauto.
    } 

    eapply T_Conv with (A := (open_tm_wrt_tm B0 a1)); auto.
    eapply Eq_SSigmaSnd; eauto 1.
    eapply Eq_Sym; eauto 1.
    eapply Eq_Sym; eauto 1.
    eapply Eq_Beta; eauto 1.
    eapply Typing_Grade; eauto.
    eapply S_Proj1Beta; eauto.
    eapply Typing_Grade; eauto using Typing_lift.
    
    eapply Typing_substitution with (a := (a_Proj1 psi0 (a_SPair a1 psi0 b))) in H10.
    rewrite <- subst_tm_tm_intro in H10;  eauto. 
    eapply T_Conv; simpl_env; eauto 2.
    eapply Eq_SSigmaFst; eauto 1.
    eapply Eq_Sym; eauto 1.
    eauto using Ctx_meet_ctx_l.
  - (* case cong *)
    clear H0.
    specialize (IHh1 ltac:(auto) _ ltac:(eauto)).
    clear IHh2 IHh3.
    move: (Typing_regularity IHh1) => TS.
    specialize (TS ltac:(auto)). destruct TS as [s0 TS].
    pick fresh x. 
    move: (H x ltac:(auto)) => TB.
    have EP: DefEq (labels (meet_ctx_l q_C W)) q_C (a_Pi q_C (a_Sum A1 A2) B) (a_Pi q_C (a_Sum A1 A2) B).
    { 
      eapply Eq_Refl.
      fresh_apply_Grade y; eauto using Typing_Grade.
      move: (@H y ltac:(auto)) => h.
      eapply Typing_Grade in h. simpl_env in h.
      auto.
    }      
    eapply T_Conv.
    eapply T_Case; eauto.
    + pick fresh y and apply Eq_Subst; auto.
      eapply Eq_Refl.
      eapply Typing_Grade in TB. simpl_env in TB.
      eapply Grade_renaming with (x:=y)(y:=x); eauto. simpl_env. rewrite dom_meet_ctx_l. auto.
      simpl_env. rewrite dom_meet_ctx_l. auto.
      eapply CDefEq_Leq. reflexivity.
      eapply Eq_Sym.
      eapply Eq_Beta; eauto using Typing_lift, Typing_Grade.
    + 
    repeat spec x.
    replace (a_Type _) with (subst_tm_tm a x (a_Type s)). 2: reflexivity.
    rewrite (subst_tm_tm_intro x). auto.
    eapply Typing_substitution; eauto using Typing_lift, Ctx_meet_ctx_l.
  - (* case inj1 *)
    have [s1 TA1]: exists s, Typing (meet_ctx_l q_C W) q_C A1 (a_Type s) .
    { move: (Typing_regularity h2 ltac:(auto)) => [s0 TP1].
      pick fresh x.
      have F2: x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B1.  rewrite dom_meet_ctx_l. auto.
      move: (@T_Pi_inversion x _ _ _ A1 B1 _ F2 TP1 ltac:(eauto using Ctx_meet_ctx_l)) => 
      [s1 [s2 [s3 h0]]].
      split_hyp. eauto. }
    have [sb TB] : exists s, Typing (meet_ctx_l q_C W) q_C (open_tm_wrt_tm B (a_Inj1 a0)) (a_Type s).
    { 
      pick fresh x.
      exists s.
      replace (a_Type s) with (subst_tm_tm (a_Inj1 a0) x (a_Type s)). 2: auto.
      rewrite (subst_tm_tm_intro x B); auto.
      eapply Typing_substitution; eauto 2.
      eapply Typing_lift; eauto.
      eapply Ctx_meet_ctx_l; eauto.
    } 

    move: (T_Inj1_inversion h1 ltac:(auto)) => [A1' [A2' hh]]. split_hyp.
    eapply T_Conv with (A := open_tm_wrt_tm B1 a0); eauto 1.
    eapply T_App; eauto.
    eapply T_Conv with (A := A1'); eauto 2 using Typing_leq_C.
    eapply Typing_subsumption; eauto using leq_join_r.
    rewrite join_leq; auto. eapply Typing_leq_C; eauto. 
    transitivity psi; auto. eapply Typing_leq_C; eauto.
    pick fresh x.
    rewrite (subst_tm_tm_intro x B1); auto.
    rewrite H1; auto.
    rewrite subst_tm_tm_open_tm_wrt_tm; auto.
    rewrite subst_tm_tm_fresh_eq; auto.
    replace (subst_tm_tm a0 x (a_Inj1 (a_Var_f x))) with (a_Inj1 a0).
    eapply Eq_Refl.
    eapply Typing_Grade; eauto.
    simpl. destruct (x == x) eqn:E. rewrite E.  auto. done.
  - (* case inj 2 *)
    have [s2 TA2] : exists s2, Typing (meet_ctx_l q_C W) q_C A2 (a_Type s2).
    { move: (Typing_regularity h3 ltac:(auto)) => [s0 TP1].
      pick fresh x.
      have F2: x `notin` dom (meet_ctx_l q_C W) \u fv_tm_tm B2.  rewrite dom_meet_ctx_l. auto.
      move: (@T_Pi_inversion x _ _ _ A2 B2 _ F2 TP1 ltac:(eauto using Ctx_meet_ctx_l)) => [s4 [s2 [s3 h0]]].
      split_hyp. eauto. }
    have [sb TB] : exists s, Typing (meet_ctx_l q_C W) q_C (open_tm_wrt_tm B (a_Inj2 a0)) (a_Type s).
    { 
      pick fresh x. eexists.
      replace (a_Type s) with (subst_tm_tm (a_Inj2 a0) x (a_Type s)). 2: auto.
      rewrite (subst_tm_tm_intro x B); auto.
      eapply Typing_substitution; eauto 2.
      eapply Typing_lift; eauto.
      eapply Ctx_meet_ctx_l; eauto.
    } 

    move: (T_Inj2_inversion h1 ltac:(auto)) => [A1' [A2' hh]]. split_hyp.
    eapply T_Conv with (A := open_tm_wrt_tm B2 a0); eauto 1.
    eapply T_App; eauto.
    eapply T_Conv with (A := A2'); eauto 2 using Typing_leq_C.
    eapply Typing_subsumption; eauto using leq_join_r.
    rewrite join_leq; auto. eapply Typing_leq_C; eauto. 
    transitivity psi; auto. eapply Typing_leq_C; eauto.
    pick fresh x.
    rewrite (subst_tm_tm_intro x B2); auto.
    rewrite H2; auto.
    rewrite subst_tm_tm_open_tm_wrt_tm; auto.
    rewrite subst_tm_tm_fresh_eq; auto.
    replace (subst_tm_tm a0 x (a_Inj2 (a_Var_f x))) with (a_Inj2 a0).
    eapply Eq_Refl.
    eapply Typing_Grade; eauto.
    simpl. destruct (x == x) eqn:E. rewrite E.  auto. done.
Qed.
