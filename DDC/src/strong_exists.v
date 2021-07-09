Require Export Qual.tactics.
Require Export Qual.typing.
Require Export Qual.consist.

Set Implicit Arguments.
Open Scope grade_scope.

(* Can we define strong existentials from weak existentials? *)


Definition wproj1 psi0 a := a_LetPair psi0 a (a_Abs q_Bot (a_Var_b 1)).
Definition wproj2 psi0 a := a_LetPair psi0 a (a_Abs q_Bot (a_Var_b 0)).

Lemma wproj1_lc : forall a1 psi0, 
    lc_tm a1 -> 
    lc_tm (a_LetPair psi0 a1 (a_Abs q_Bot (a_Var_b 1))).
Proof.
  intros.
  eapply (lc_a_LetPair); auto.
  intro z.
  cbn.
  eapply (lc_a_Abs_exists z).
  cbn.
  eauto.
Qed.



Lemma wproj2_lc : forall a1 psi0, 
    lc_tm a1 -> 
    lc_tm (a_LetPair psi0 a1  (a_Abs q_Bot (a_Var_b 0))).
Proof.
  intros.
  eapply (lc_a_LetPair); auto.
  intro z.
  cbn.
  eapply (lc_a_Abs_exists z).
  cbn.
  eauto.
Qed.

Local Hint Resolve wproj1_lc wproj2_lc : core.


Lemma wproj1_beta : forall a1 a2 psi0, 
    lc_tm a1 -> lc_tm a2 ->
    exists b, Step (wproj1 psi0 (a_WPair a1 psi0 a2)) b /\ Step b a1.
Proof. 
  intros. unfold wproj1.
  eexists.
  split.
  + eapply S_LetPairBeta; auto.
  + cbn.
    replace a1 with (open_tm_wrt_tm a1 a2) at 2.
    eapply S_Beta; auto.
    eapply lc_a_Abs. intro x. 
    rewrite open_tm_wrt_tm_lc_tm; auto.
    rewrite open_tm_wrt_tm_lc_tm; auto.
Qed.

Lemma wproj2_beta : forall a1 a2 psi0, 
    lc_tm a1 -> lc_tm a2 ->
    exists b, Step (wproj2 psi0 (a_WPair a1 psi0 a2)) b /\ Step b a2.
Proof. 
  intros. unfold wproj2.
  eexists.
  split.
  eapply S_LetPairBeta; eauto.
  cbn.
  replace a2 with (open_tm_wrt_tm (a_Var_b 0) a2) at 2.
  eapply S_Beta; eauto.
  eapply (lc_a_Abs). move=> z.
  cbn. auto.
  cbn.
  auto.
Qed.
  

Lemma T_wproj1
     : forall (W : context) (psi psi0 : grade) (a A B : tm),
       Typing W psi a (a_WSigma psi0 A B) -> psi0 <= psi -> Ctx W -> 
       Typing W psi (wproj1 psi0 a) A.
Proof.
  intros.
  move: (Typing_regularity H H1) => TW.
  unfold wproj1.
  pick fresh z for (fv_tm_tm A). 
  replace A with (open_tm_wrt_tm (close_tm_wrt_tm z A) a). 
  2 : { rewrite <- subst_tm_tm_spec. rewrite subst_tm_tm_fresh_eq; auto. }
  move: (Typing_uniq TW) => u.

  pick fresh x and apply T_LetPair.
  + have Frz: x `notin` union (dom (meet_ctx_l q_C W)) (fv_tm_tm B); try rewrite dom_meet_ctx_l; eauto.
    move: (@T_WSigma_inversion x _ _ _ _ _ _ Frz TW ltac:(eauto using Ctx_meet_ctx_l)) => hh. split_hyp.
    move: (Typing_uniq H3) => uu.
    
    rewrite <- subst_tm_tm_spec.
    rewrite subst_tm_tm_fresh_eq; auto.
    eapply Typing_weakening; eauto. 

  + eauto.
  + move=> y Fry.
    cbn. simpl_env.
    pick fresh w and apply T_Abs.
    ++ cbn.
       rewrite <- subst_tm_tm_spec.
       rewrite <- subst_tm_tm_spec.
       rewrite (subst_tm_tm_fresh_eq A). auto.
       rewrite (subst_tm_tm_fresh_eq A). auto.
       simpl_env.
       eapply T_Var with (psi0 := psi0 * psi); eauto.
       econstructor; eauto.
       econstructor; eauto using Typing_uniq.
       rewrite join_leq; auto. reflexivity.
       eapply Typing_leq_C; eauto.
    ++ simpl_env.
       have Frz: x `notin` union (dom (meet_ctx_l q_C W)) (fv_tm_tm B); try rewrite dom_meet_ctx_l; eauto.
       move: (@T_WSigma_inversion x _ _ _ _ _ _ Frz TW ltac:(eauto using Ctx_meet_ctx_l)) => hh. split_hyp.
       move: (Typing_uniq H3) => uu.
       pick fresh w and apply T_Pi.
       rewrite meet_mult. eapply Typing_leq_C; eauto.
       eapply Typing_pumping. eapply Typing_leq_C; eauto.
       eapply Typing_narrowing; eauto.
       econstructor; eauto using ctx_sub_refl.
       eapply leq_meet_l.
       rewrite <- subst_tm_tm_spec.
       rewrite <- subst_tm_tm_spec.
       rewrite (subst_tm_tm_fresh_eq A). auto.
       rewrite (subst_tm_tm_fresh_eq A). auto.
       eapply Typing_weakening.
       eapply Typing_weakening; auto.
       econstructor; eauto.
       simpl. rewrite dom_meet_ctx_l. auto.
Qed.

Lemma T_WProj2
     : forall (W : context) (psi psi0 : grade) (a B A : tm),
       Typing W psi a (a_WSigma psi0 A B) -> Ctx W -> 
       (psi0 <= q_C) -> 
       Typing W psi (wproj2 psi0 a) (open_tm_wrt_tm B (wproj1 psi0 a)).
Proof.
  intros.
  move: (Typing_regularity H H0) => TW.
  move: (Typing_leq_C H) => LP.
  move: (Typing_Grade TW) => GW.
  move: (Typing_uniq H) => uh.
  move: (Typing_uniq TW) => uw.
  unfold wproj2.
  pick fresh z for (fv_tm_tm B \u fv_tm_tm a \u dom W).
  replace (open_tm_wrt_tm B (wproj1 psi0 a)) with 
      (open_tm_wrt_tm (close_tm_wrt_tm z (open_tm_wrt_tm B (wproj1 psi0 (a_Var_f z)))) a).
  2: { rewrite <- subst_tm_tm_spec.
       rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc1.
       rewrite subst_tm_tm_fresh_eq. auto.
       f_equal.
       cbn. unfold wproj1.
       f_equal.
       destruct (z == z) eqn:E. rewrite E. done. done. }
  pick fresh x and apply T_LetPair.
  - (* result type is well formed. *)
    rewrite <- subst_tm_tm_spec.
    rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc1.
    rewrite (subst_tm_tm_fresh_eq B); auto.
    cbn. destruct (z ==z) eqn:E. rewrite E. 2: done. simpl_env. clear e E.

    (* invert well-formedness of Sigma type. (TW) *)
    pick fresh y.
    have Ux:  uniq ([(x, (q_C, a_WSigma psi0 A B))] ++ meet_ctx_l q_C W).
    { econstructor; try rewrite dom_meet_ctx_l; eauto. }
    have Uyx: uniq ([(y, (q_C, A))] ++ [(x, (q_C, a_WSigma psi0 A B))] ++ meet_ctx_l q_C W).
    { econstructor; eauto.  simpl.  rewrite dom_meet_ctx_l; eauto. }
    have Frz: y `notin` union (dom (meet_ctx_l q_C W)) (fv_tm_tm B); try rewrite dom_meet_ctx_l; eauto.
    move: (@T_WSigma_inversion y _ _ _ _ _ _ Frz TW ltac:(eauto using Ctx_meet_ctx_l)) => hh. split_hyp.

    rewrite (subst_tm_tm_intro y); eauto.
    fold (wproj1 psi0 (a_Var_f x)).
    replace a_Type with (subst_tm_tm (wproj1 psi0 (a_Var_f x)) y a_Type). 2: auto.
    eapply Typing_substitution; simpl_env; eauto using Ctx_meet_ctx_l.
    eapply Typing_weakening_middle; eauto. 
    eapply T_wproj1; auto.
    eapply T_Var with (psi0 := q_C); eauto using q_leb_refl. 
    econstructor; eauto using Ctx_meet_ctx_l. simpl_env. eauto. rewrite dom_meet_ctx_l; eauto.
    econstructor; eauto using Ctx_meet_ctx_l. simpl_env. eauto. rewrite dom_meet_ctx_l; eauto.

  - (* a is a sigma *) auto.    
  - (* body has right type *) 
    move=> y Fry.
    cbn. simpl_env.
    have TBP1: forall w, w `notin` {{x}} \u fv_tm_tm A \u dom (meet_ctx_l q_C W) ->
      Typing
        ([(w, (q_C, open_tm_wrt_tm B (a_Var_f x)))] ++ [(x, (q_C + psi0 * psi, A))] ++ meet_ctx_l q_C W)
        q_C (open_tm_wrt_tm B (a_LetPair psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f w)) (a_Abs q_Bot (a_Var_b 1))))
        a_Type.
    { 
      intros w Frw.
      remember (a_LetPair psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f w)) (a_Abs q_Bot (a_Var_b 1))) as a1.

      pick fresh xx.
      have Frz: xx `notin` union (dom (meet_ctx_l q_C W)) (fv_tm_tm B); try rewrite dom_meet_ctx_l; eauto.
      move: (@T_WSigma_inversion xx _ _ _ _ _ _ Frz TW ltac:(eauto using Ctx_meet_ctx_l)) => hh. split_hyp.

      remember (open_tm_wrt_tm B (a_Var_f x)) as Bx.
      have TBx:  Typing (meet_ctx_l q_C ([(x, (q_C + psi0 * psi, A))] ++ meet_ctx_l q_C W)) q_C Bx a_Type.
      {
        rewrite HeqBx. simpl_env.
        eapply Typing_narrowing with (W1 := [(x, (q_C, A))] ++ meet_ctx_l q_C W).
        2: { econstructor; try rewrite dom_meet_ctx_l; eauto. eapply leq_meet_l. eapply ctx_sub_refl; auto. }
        eapply (@Typing_rename_Type xx).
        auto.
        rewrite dom_meet_ctx_l. auto.
        auto.
        econstructor; eauto using Ctx_meet_ctx_l. simpl_env. auto.
        rewrite dom_meet_ctx_l. auto.        
      }

      rewrite (subst_tm_tm_intro xx); auto.
      replace a_Type with (subst_tm_tm a1 xx a_Type). 2: auto.

      eapply Typing_weakening_middle with (W := [(w, (q_C, Bx))] ++ [(x, (q_C + psi0 * psi, A))]) in H3.
      2: { simpl. repeat econstructor; try rewrite dom_meet_ctx_l; eauto. } 
      have Tp1 : Typing ([(w, (q_C, Bx))] ++ [(x, (q_C + psi0 * psi, A))] ++ meet_ctx_l q_C W) q_C  a1 A.
      { 
        rewrite Heqa1.
        eapply Typing_narrowing with (W1 := [(w, (q_C, Bx))] ++ [(x, (q_C, A))] ++ meet_ctx_l q_C W).
        2: { econstructor; try rewrite dom_meet_ctx_l; eauto. reflexivity. 
             econstructor; try rewrite dom_meet_ctx_l; eauto. eapply leq_meet_l. eapply ctx_sub_refl; auto. }
        fold (wproj1 psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f w))).
        eapply T_wproj1; eauto.
        have UU: uniq ([(w, (q_C, Bx))] ++ [(x, (q_C, A))] ++ meet_ctx_l q_C W).
        {  econstructor; auto. econstructor; eauto. rewrite dom_meet_ctx_l. auto. }
        eapply T_WPair; auto.
        simpl_env. repeat rewrite meet_idem.
        eapply Typing_weakening with (W2 := [(w, (q_C, Bx))] ++ [(x, (q_C, A))]); eauto.
        eapply T_Var with (psi0:= q_C); auto.
        eapply leq_join_r.
        rewrite join_leq; auto. reflexivity.
        rewrite HeqBx.
        eapply T_Var with (psi0:= q_C); auto.
        econstructor; eauto. econstructor; eauto. rewrite dom_meet_ctx_l. auto. reflexivity. reflexivity.
        econstructor; eauto. econstructor; eauto using Ctx_meet_ctx_l.
        simpl_env; auto. rewrite dom_meet_ctx_l. auto.
        simpl_env. rewrite meet_idem.
        simpl_env in TBx.
        apply Typing_pumping with (psi1 := q_C) in TBx; try reflexivity.
        rewrite join_leq in TBx.
        eapply leq_meet_l.
        auto.
      }

      eapply Typing_substitution; eauto. 
      econstructor; eauto. econstructor; simpl_env; eauto using Ctx_meet_ctx_l.
      rewrite dom_meet_ctx_l. auto.
    } 
      
    pick fresh w and apply T_Abs.
    ++ rewrite join_leq. apply leq_Bot.
       rewrite <- subst_tm_tm_spec.
       rewrite <- subst_tm_tm_spec.
       rewrite subst_tm_tm_open_tm_wrt_tm; eauto.
       cbn. simpl_env. destruct (z == z) eqn:E. rewrite E. 2: done.
       rewrite (subst_tm_tm_fresh_eq B). auto.
       rewrite subst_tm_tm_open_tm_wrt_tm; eauto.
       rewrite (subst_tm_tm_fresh_eq B). auto.
       cbn. destruct (x == y) eqn:E2. rewrite E2. subst. clear Fr1 Fr. fsetdec.
       rewrite E2. destruct (y == y) eqn:E3. rewrite E3. 2: done.
       simpl_env.
       eapply T_Conv with (A := open_tm_wrt_tm B (a_Var_f x)).
       eapply T_Var with (psi0:= psi); auto. reflexivity. 
       eapply Eq_Sym.
       eapply Eq_PiSnd.
       eapply Eq_Refl.
       inversion GW; subst.
       simpl_env.
       eapply Grade_weakening_middle with (P3 := [(w, q_C + psi)] ++ [(x, q_C + psi0 * psi)]) (P2:=nil).
       simpl_env.
       pick fresh v and apply G_Pi; auto.
       simpl_env. econstructor; eauto. econstructor; eauto. rewrite labels_dom. rewrite dom_meet_ctx_l. auto.
       simpl. rewrite labels_dom. rewrite dom_meet_ctx_l. auto.
       simpl_env.
       have GA: Grade ([(w, q_C + psi)] ++ [(x, q_C + psi0 * psi)] ++ labels (meet_ctx_l q_C W)) q_C
                      (a_LetPair psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f w)) (a_Abs q_Bot (a_Var_b 1))).
       { 
         have Fw: x `notin` dom (labels (meet_ctx_l q_C W)). rewrite labels_dom. rewrite dom_meet_ctx_l. auto.
         fresh_apply_Grade xx.
         eapply G_WPairRel.
         eapply G_Var; auto.
         econstructor; eauto. simpl_env. rewrite dom_meet_ctx_l. auto.
         eapply leq_meet_l.
         eapply G_Var; auto.
         econstructor; eauto. simpl_env. rewrite dom_meet_ctx_l. auto.
         eapply leq_meet_l.
         auto.
         cbn. simpl_env.
         fresh_apply_Grade yy.
         cbn. simpl_env.
         eapply G_Var; auto.
         econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
         econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
         econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
         auto.
       } 

       have GB: Grade ([(w, q_C + psi)] ++ [(x, q_C + psi0 * psi)] ++ labels (meet_ctx_l q_C W)) q_C
                        (a_App (open_tm_wrt_tm (a_Abs q_Bot (a_Var_b 1)) (a_Var_f x)) q_Bot (a_Var_f w)). 
       { 
         eapply G_AppRel; auto using leq_Bot.
         + cbn. simpl_env.
           fresh_apply_Grade xx. cbn. simpl_env.
           eapply G_Var; auto.
           econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
           econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
           econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
           apply leq_meet_l.
         + eapply G_Var; auto.
           econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
           econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
           apply leq_meet_l.
       }
       eapply Eq_Trans.
       eapply Eq_Beta; auto.
       eapply Eq_Beta; auto.
       cbn.
       replace (a_Var_f x) with (open_tm_wrt_tm (a_Var_f x) (a_Var_f w)) at 2.
       eapply S_Beta; auto. econstructor; eauto. intros xx. cbn. auto. cbn. auto.
       eapply G_Var; auto. econstructor; eauto. econstructor; eauto. 
       rewrite labels_dom. rewrite dom_meet_ctx_l. auto.
       simpl. rewrite labels_dom. rewrite dom_meet_ctx_l. auto.
       rewrite meet_mult; auto.
       rewrite join_lub; auto.
       eapply leq_meet_l; auto.
       simpl_env.
       eapply Typing_narrowing.
       eapply TBP1.
       rewrite dom_meet_ctx_l; auto.
       repeat econstructor; eauto using ctx_sub_refl, leq_meet_l, q_leb_refl.
       all: simpl; rewrite dom_meet_ctx_l.
       all: auto.
    ++ simpl_env.
       have Frz: x `notin` union (dom (meet_ctx_l q_C W)) (fv_tm_tm B); try rewrite dom_meet_ctx_l; eauto.
       move: (@T_WSigma_inversion x _ _ _ _ _ _ Frz TW ltac:(eauto using Ctx_meet_ctx_l)) => hh. split_hyp.

       pick fresh w and apply T_Pi; auto.
       rewrite meet_mult; auto.
       eapply Typing_pumping; auto.
       eapply Typing_narrowing; eauto using leq_meet_l, ctx_sub_refl.
       rewrite <- subst_tm_tm_spec.
       rewrite <- subst_tm_tm_spec.
       rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc1.
       rewrite (subst_tm_tm_fresh_eq B); auto.
       rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc1.
       rewrite (subst_tm_tm_fresh_eq B); auto.
       cbn. destruct (z == z) eqn:E. rewrite E. 2:done. 
       cbn. destruct (x == y) eqn:E2; rewrite E2. subst. clear Frz Fr0 Fr1 Fr. fsetdec.
       destruct (y == y) eqn:E3. rewrite E3. 2:done. simpl_env.
       eapply TBP1.
       rewrite dom_meet_ctx_l; auto.
Unshelve.
eapply q_C.
Qed.
