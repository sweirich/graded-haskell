Require Export Qual.tactics.
Require Export Qual.typing.
Require Export Qual.consist.

Set Implicit Arguments.
Open Scope grade_scope.

(* Can we define strong existentials from weak existentials? *)

(* This file relies on two axioms related to variable renaming. *)


Definition wproj1 psi0 a B := a_LetPair psi0 a (a_Abs q_Bot B (a_Var_b 1)).
Definition wproj2 psi0 a B := a_LetPair psi0 a (a_Abs q_Bot B (a_Var_b 0)).

Local Hint Resolve lc_body_tm_wrt_tm : core.

Lemma wproj1_lc : forall a1 psi0 B, 
    lc_tm a1 -> body_tm_wrt_tm B ->
    lc_tm (a_LetPair psi0 a1 (a_Abs q_Bot B (a_Var_b 1))).
Proof.
  intros.
  eapply (lc_a_LetPair); auto.
  intro z.
  cbn.
  eapply (lc_a_Abs_exists z).
  + replace (open_tm_wrt_tm_rec 0 (a_Var_f z) B) with 
        (open_tm_wrt_tm B (a_Var_f z)). 2: reflexivity.
    eauto.
  + cbn. eauto.
Qed.



Lemma wproj2_lc : forall a1 psi0 A, 
    lc_tm a1 -> body_tm_wrt_tm A ->
    lc_tm (a_LetPair psi0 a1  (a_Abs q_Bot A (a_Var_b 0))).
Proof.
  intros.
  eapply (lc_a_LetPair); auto.
  intro z.
  cbn.
  eapply (lc_a_Abs_exists z).
  + replace (open_tm_wrt_tm_rec 0 (a_Var_f z) A) with 
        (open_tm_wrt_tm A (a_Var_f z)). 2: reflexivity.
    eauto.
  + cbn.
  eauto.
Qed.

Local Hint Resolve wproj1_lc wproj2_lc : core.


Lemma wproj1_beta : forall a1 a2 psi0 A, 
    lc_tm a1 -> lc_tm a2 ->  body_tm_wrt_tm A ->
    exists b, Step (wproj1 psi0 (a_WPair a1 psi0 a2) A) b /\ Step b a1.
Proof. 
  intros. unfold wproj1.
  eexists.
  split.
  + eapply S_LetPairBeta; auto.
  + cbn.
    replace (open_tm_wrt_tm_rec 0 a1 A) with 
        (open_tm_wrt_tm A a1). 2: reflexivity.
    replace a1 with (open_tm_wrt_tm a1 a2) at 3.
    eapply S_Beta; eauto.
    eapply lc_a_Abs; eauto. intro x. 
    rewrite open_tm_wrt_tm_lc_tm; auto.
    rewrite open_tm_wrt_tm_lc_tm; auto.
Qed.

Lemma wproj2_beta : forall a1 a2 psi0 A, 
    lc_tm a1 -> lc_tm a2 ->  body_tm_wrt_tm A ->
    exists b, Step (wproj2 psi0 (a_WPair a1 psi0 a2) A) b /\ Step b a2.
Proof. 
  intros. unfold wproj2.
  eexists.
  split.
  eapply S_LetPairBeta; eauto.
  cbn.
  replace (open_tm_wrt_tm_rec 0 a1 A) with 
        (open_tm_wrt_tm A a1). 2: reflexivity.
  replace a2 with (open_tm_wrt_tm (a_Var_b 0) a2) at 2.
  eapply S_Beta; eauto.
  eapply (lc_a_Abs); eauto. move=> z.
  cbn. auto.
  cbn.
  auto.
Qed.

(*  
Typing_open:
  forall (x : atom) (psi0 : grade) (A : tm) (W : list (atom * (grade * tm)))
    (psi : grade) (b a B : tm),
  x `notin` union (fv_tm_tm b) (fv_tm_tm B) ->
  Typing ([(x, (psi0, A))] ++ W) psi (open_tm_wrt_tm b (a_Var_f x))
    (open_tm_wrt_tm B (a_Var_f x)) ->
  Typing W psi0 a A ->
  Ctx W -> Typing W psi (open_tm_wrt_tm b a) (open_tm_wrt_tm B a)
*)
Lemma T_Abs_exists
     : forall x (W : context) (psi psi0 : grade) 
         (A b B : tm) (s : sort),
        x `notin` dom W \u fv_tm_tm A \u fv_tm_tm B \u fv_tm_tm b ->
        Typing ([(x, (psi0 * psi, A))] ++ W) psi
          (open_tm_wrt_tm b (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) ->
       Typing (meet_ctx_l q_C W) q_C (a_Pi psi0 A B) (a_Type s) ->
       Ctx ([(x, (psi0 * psi, A))] ++ W) ->
       Typing W psi (a_Abs psi0 A b) (a_Pi psi0 A B).
Proof.
  intros.
  move: (Typing_uniq H0) => u.
  move: (Typing_leq_C H0) => LE.
  pick fresh y and apply T_Abs; eauto.
  eapply (@Typing_rename x y); eauto.
  inversion H2. subst.
  econstructor; eauto.
Qed.

Lemma T_Pi_exists 
     : forall x (W : context) (psi psi0 : grade) 
         (A B : tm) (s3 s1 s2 : sort),
       Typing W psi A (a_Type s1) ->
       Typing ([(x, (psi, A))] ++ W) psi (open_tm_wrt_tm B (a_Var_f x))
          (a_Type s2) ->
       Ctx ([(x, (psi0 * psi, A))] ++ W) ->
       x `notin` fv_tm_tm A \u fv_tm_tm B ->
       rule s1 s2 s3 -> Typing W psi (a_Pi psi0 A B) (a_Type s3).
Proof. 
  intros.
  move: (Typing_uniq H0) => u.
  move: (Typing_leq_C H0) => LE.
  pick fresh y and apply T_Pi; eauto.
  eapply (@Typing_rename_Type x y); eauto.
  inversion H1. subst.
  econstructor; eauto.
Qed.

Lemma close_tm_wrt_tm_rename : forall a x y, 
    y `notin` fv_tm_tm a ->
    close_tm_wrt_tm x a = close_tm_wrt_tm y (subst_tm_tm (a_Var_f y) x a). 
Proof.
  unfold close_tm_wrt_tm.
  intros a x y.
  generalize 0. 
  induction a; intros; simpl; auto.
  all: simpl in H.
  all: try rewrite IHa1.
  all: try rewrite IHa2.
  all: try rewrite IHa3.
  all: try rewrite IHa.
  all: auto.
  (* x0 is the current free variable. *)
  destruct (x == x0) eqn:EX; subst.
  + (* we found it! *)
    rewrite EX. simpl. 
    rewrite eq_dec_refl. auto.
  + destruct (x0 == x) eqn:EX0. subst. done.
    simpl.
    destruct (y == x0) eqn:EY. subst. assert False. apply H. auto. done.
    rewrite EY. auto.
Qed.

Lemma LetPair_rename : 
  forall x z y psi0 psi A B W c C, 
  x `notin` {{y}} \u fv_tm_tm A \u fv_tm_tm B \u fv_tm_tm C \u fv_tm_tm c  ->
  z `notin` {{x}} \u {{y}} \u dom W \u fv_tm_tm A \u fv_tm_tm B \u fv_tm_tm C \u fv_tm_tm c  ->  
  Ctx ([(z, (psi0 * psi, A))] ++ W) ->  
  Typing ([(x, (psi0 * psi, A))] ++ W) psi (open_tm_wrt_tm c (a_Var_f x))
    (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f x))
       (close_tm_wrt_tm y
          (open_tm_wrt_tm C (a_WPair (a_Var_f x) psi0 (a_Var_f y))))) ->

  Typing ([(z, (psi0 * psi, A))] ++ W) psi (open_tm_wrt_tm c (a_Var_f z))
    (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f z))
       (close_tm_wrt_tm y
          (open_tm_wrt_tm C (a_WPair (a_Var_f z) psi0 (a_Var_f y))))).
Proof. 
  intros.
  move: H2 => H4.
  move: (Typing_uniq H4) => u.
  eapply Typing_weakening_middle with (W:= (z ~ (psi0 * psi, A))) in H4.
  2: { destruct_uniq. solve_uniq. } 
  move: (@Typing_substitution_CTyping x (psi0 * psi) A _ nil _ _ (a_Var_f z) _ H4) => h4.
  simpl in h4. simpl_env in h4.
  repeat rewrite subst_tm_tm_open_tm_wrt_tm in h4; auto.
  rewrite subst_tm_tm_var in h4; auto.
  rewrite subst_tm_tm_fresh_eq in h4. auto.
  rewrite subst_tm_tm_fresh_eq in h4. auto.
  rewrite subst_tm_tm_close_tm_wrt_tm in h4; auto.
  repeat rewrite subst_tm_tm_open_tm_wrt_tm in h4; auto.
  replace (subst_tm_tm (a_Var_f z) x
                (a_WPair (a_Var_f x) psi0 (a_Var_f y))) with 
    (a_WPair (subst_tm_tm (a_Var_f z) x (a_Var_f x)) psi0 
             (subst_tm_tm (a_Var_f z) x (a_Var_f y))) in h4. 2: auto.
  rewrite subst_tm_tm_var in h4. 
  rewrite subst_tm_tm_var_neq in h4.
  auto.
  rewrite subst_tm_tm_fresh_eq in h4. auto.
  eapply h4. auto.
  destruct (order_q_C_dec (psi0 * psi)) eqn:LT.
  + eapply CT_Leq; auto.
    eapply T_Var; eauto. solve_uniq.
    reflexivity.
  + eapply CT_Top; auto.
    simpl_env.
    eapply T_Var; eauto. econstructor. eapply meet_ctx_l_uniq. inversion u. auto.
    rewrite dom_meet_ctx_l. auto.
    eapply leq_meet_l.
    reflexivity.
Qed.

(* A version of the LetPair typing rule *)
Lemma T_LetPair_exists 
     : forall x y (W : context) (psi psi0 : grade) (a c C B A : tm) (s : sort),
        Typing ([(x, (q_C, a_WSigma psi0 A B))] ++ meet_ctx_l q_C W) q_C
          (open_tm_wrt_tm C (a_Var_f x)) (a_Type s) ->
       Typing W psi a (a_WSigma psi0 A B) ->
       x `notin` fv_tm_tm (a_WSigma psi0 A B) \u fv_tm_tm C \u fv_tm_tm c  ->
       y `notin` fv_tm_tm C \u dom (meet_ctx_l q_C W) \u (singleton x) ->
       Ctx ([(x, (q_C, a_WSigma psi0 A B))] ++ W) ->
        Typing ([(x, (psi0 * psi, A))] ++ W) psi
          (open_tm_wrt_tm c (a_Var_f x))
          (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f x))
             (close_tm_wrt_tm y
                (open_tm_wrt_tm C (a_WPair (a_Var_f x) psi0 (a_Var_f y))))) ->
       Typing W psi (a_LetPair psi0 a c) (open_tm_wrt_tm C a).
Proof.
  intros.
  move: (Typing_uniq H0) => u.
  move: (Typing_leq_C H0) => LE.
  pick fresh z and apply T_LetPair; eauto.
  eapply (@Typing_rename_Type x z); try rewrite dom_meet_ctx_l; eauto.

  inversion H3. subst.
  econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto using Ctx_meet_ctx_l.
  move=> w Frw.

  replace Qualitative_ott.close_tm_wrt_tm with close_tm_wrt_tm. 2: { auto. } 
  (* need to rename w to y *)

  erewrite close_tm_wrt_tm_rename. instantiate (1:=y). 
  2: { rewrite fv_tm_tm_open_tm_wrt_tm_upper. simpl. auto. }

  rewrite subst_tm_tm_open_tm_wrt_tm; auto.
  rewrite subst_tm_tm_fresh_eq. auto.
  replace (subst_tm_tm (a_Var_f y) w
                (a_WPair (a_Var_f z) psi0 (a_Var_f w))) with 
    (a_WPair (subst_tm_tm (a_Var_f y) w (a_Var_f z)) psi0 
             (subst_tm_tm (a_Var_f y) w (a_Var_f w))). 2: auto.
  rewrite subst_tm_tm_var. rewrite subst_tm_tm_var_neq. auto.
                    
  simpl in H1.

  inversion H3. subst.
  have Frz: z `notin`  union (dom (meet_ctx_l q_C W)) (fv_tm_tm B).
  rewrite dom_meet_ctx_l. auto.
  move: (@T_WSigma_inversion z _ _ _ _ _ _ Frz H10 ltac:(eauto using Ctx_meet_ctx_l)) => 
    [s1 [s2 [s3 hh]]]. split_hyp.

  eapply LetPair_rename with (x:= x); auto.
  econstructor; eauto using Ctx_meet_ctx_l.
Qed.  

Axiom rename1: forall x y w y0 psi0 psi A W B s, 
 x `notin` union (fv_tm_tm B) (dom W) ->
 y `notin` union (fv_tm_tm A) (union (fv_tm_tm B) (dom W)) ->
 w `notin` union (fv_tm_tm B) (dom W) ->
 y0 `notin` union (fv_tm_tm A) (union (fv_tm_tm B) (dom W)) ->
 Typing ([(x, (q_C + psi0 * psi, A))] ++ meet_ctx_l q_C W) q_C
         (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f x)) (close_tm_wrt_tm y A))
         (a_Type s) ->
  Typing ([(w, (q_C + psi0 * psi, A))] ++ meet_ctx_l q_C W) q_C
         (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f w)) (close_tm_wrt_tm y0 A))
         (a_Type s).

Axiom rename2: forall x y w y0 psi0 psi A W B s', 
    x `notin` union (fv_tm_tm B) (dom W) ->
    y `notin` union (fv_tm_tm A) (union (fv_tm_tm B) (dom W)) ->
    w `notin` union (fv_tm_tm B) (dom W) ->
    y0 `notin` union (fv_tm_tm A) (union (fv_tm_tm B) (dom W)) ->
  Typing (meet_ctx_l q_C ([(x, (psi0 * psi, A))] ++ W)) q_C
         (a_Pi q_Bot
               (open_tm_wrt_tm B (a_Var_f x))
               (close_tm_wrt_tm y
                  (open_tm_wrt_tm B (wproj1 psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f y)) B)))) 
         (a_Type s') ->
  Typing (meet_ctx_l q_C ([(w, (psi0 * psi, A))] ++ W)) q_C
         (a_Pi q_Bot
               (open_tm_wrt_tm B (a_Var_f w))
               (close_tm_wrt_tm y0
                  (open_tm_wrt_tm B (wproj1 psi0 (a_WPair (a_Var_f w) psi0 (a_Var_f y0)) B)))) 
         (a_Type s').


Lemma T_wproj1
     : forall (W : context) (psi psi0 : grade) (a A B : tm) s x y,
       Typing W psi a (a_WSigma psi0 A B) -> psi0 <= psi -> Ctx W -> 
       (* need to ensure that type of abstraction is well formed. *)
       x `notin` fv_tm_tm B \u dom W ->
       y `notin` fv_tm_tm A \u fv_tm_tm B \u dom W ->
       Typing (meet_ctx_l q_C ([(x, (psi0 * psi, A))] ++ W)) q_C
              (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f x)) (close_tm_wrt_tm y A))
              (a_Type s) ->
       Typing W psi (wproj1 psi0 a B) A.

Proof.
  intros.
  move: (Typing_regularity H H1) => [s0 TW].
  unfold wproj1.
  replace A with (open_tm_wrt_tm (close_tm_wrt_tm y A) a). 
  2 : { rewrite <- subst_tm_tm_spec. rewrite subst_tm_tm_fresh_eq; auto. }
  move: (Typing_uniq TW) => u.

  have Fry: x `notin` union (dom (meet_ctx_l q_C W)) (fv_tm_tm B); try rewrite dom_meet_ctx_l; eauto.
  move: (@T_WSigma_inversion x _ _ _ _ _ _ ltac:(auto) TW ltac:(eauto using Ctx_meet_ctx_l)) => 
    [s1 [s2 [s3 hh]]]. split_hyp.
  clear Fry.

  pick fresh w and apply T_LetPair. 
  instantiate (3:= A).  instantiate(2:=B). instantiate (1:=s1).
  + rewrite <- subst_tm_tm_spec.
    replace (a_Type s1) with (subst_tm_tm (a_Var_f x) y (a_Type s1)).
    repeat rewrite subst_tm_tm_fresh_eq; eauto.
    eapply Typing_weakening; eauto.
    econstructor; eauto. rewrite dom_meet_ctx_l; eauto.
    auto.
  + eauto.
  + move=> y0 Fry.
    rewrite <- subst_tm_tm_spec.
    rewrite (subst_tm_tm_fresh_eq A). auto.
    cbn. simpl_env. 
    replace  (open_tm_wrt_tm_rec 0 (a_Var_f x) B) with (open_tm_wrt_tm B (a_Var_f x)). 2: auto.

    replace Qualitative_ott.close_tm_wrt_tm with close_tm_wrt_tm. 2: auto.

    eapply (@T_Abs_exists y).
    ++ 
       rewrite fv_tm_tm_open_tm_wrt_tm_upper.
       rewrite fv_tm_tm_close_tm_wrt_tm.
       simpl.
       { auto. }
    ++ cbn.
       simpl_env.
       eapply T_Var with (psi0 := psi0 * psi); eauto.
       econstructor; eauto.
       econstructor; eauto using Typing_uniq.
       rewrite join_leq; auto. reflexivity.
       rewrite <- subst_tm_tm_spec.
       rewrite (subst_tm_tm_fresh_eq A). auto.       
       eauto.
       eapply Typing_leq_C; eauto.
    ++ 
       simpl_env.
       simpl_env in H4.
       move: (Typing_uniq H4) => uu.
       instantiate (1:= s).
       eapply (@rename1 x y w y0); eauto.
    ++ econstructor. eauto.
       simpl_env.
       eapply (@Typing_rename_Type x); eauto.
       rewrite dom_meet_ctx_l; eauto.
       eapply Typing_narrowing; eauto.
       econstructor; eauto.
       eapply leq_meet_l; auto. eapply ctx_sub_refl. auto. 
       all: try rewrite dom_meet_ctx_l; eauto.
       econstructor; eauto using Ctx_meet_ctx_l.
       simpl_env. eauto.
       all: try rewrite dom_meet_ctx_l; eauto.
Qed.

Lemma T_WProj2
     : forall (W : context) (psi psi0 : grade) (a B A : tm) s s' x y,
       Typing W psi a (a_WSigma psi0 A B) -> Ctx W -> 
       (psi0 <= q_C) -> 
       (* Check typing of:  Pi y:B[x]. A *)
       (* Need to know that the Pi-type of wproj1 is well sorted. This doesn't 
        necessarily follow from the rules unless we know that 
        rule s1 s2 s3 implies rule s2 s1 s3' *)
       x `notin` fv_tm_tm A \u fv_tm_tm B \u dom W ->
       y `notin` fv_tm_tm A \u fv_tm_tm B \u dom W  \u fv_tm_tm a \u {{x}} ->
       Typing (meet_ctx_l q_C ([(x, (psi0 * q_C, A))] ++ W)) q_C
              (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f x)) (close_tm_wrt_tm y A))
              (a_Type s) ->
       (* Check typing of: Pi y:B[x]. B [proj1 (x,y)] *)
       (* Need to know that the Pi-type of wproj2 is well sorted. This doesn't 
          necessarily follow from the rules unless we know that 
          rule s1 s2 s3 implies rule s2 s2 s3' *)
       Typing (meet_ctx_l q_C ([(x, (psi0 * psi, A))] ++ W)) q_C
              (a_Pi q_Bot
                    (open_tm_wrt_tm B (a_Var_f x))
                    (close_tm_wrt_tm y
                       (open_tm_wrt_tm B (wproj1 psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f y)) B)))) 
              (a_Type s') ->
       Typing W psi (wproj2 psi0 a B) (open_tm_wrt_tm B (wproj1 psi0 a B)).
Proof.
  intros W psi psi0 a B A s s' x0 y0. intros.
  move: (Typing_regularity H H0) => [s0 TW].
  move: (Typing_leq_C H) => LP.
  move: (Typing_Grade TW) => GW.
  move: (Typing_uniq H) => uh.
  move: (Typing_uniq TW) => uw.
  unfold wproj2.

  (* invert well-formedness of Sigma type. (TW) *)
  have Frz: x0 `notin` union (dom (meet_ctx_l q_C W)) (fv_tm_tm B); try rewrite dom_meet_ctx_l; eauto.
  move: (@T_WSigma_inversion x0 _ _ _ _ _ _ Frz TW ltac:(eauto using Ctx_meet_ctx_l)) => [s1 [s2 [s3 hh]]]. split_hyp.

  (* get letPair into shape *)
  pick fresh z for (fv_tm_tm B \u fv_tm_tm a \u dom W).
  replace (open_tm_wrt_tm B (wproj1 psi0 a B)) with 
      (open_tm_wrt_tm (close_tm_wrt_tm z (open_tm_wrt_tm B (wproj1 psi0 (a_Var_f z) B))) a).
  2: { rewrite <- subst_tm_tm_spec.
       rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc1.
       rewrite subst_tm_tm_fresh_eq. auto.
       f_equal.
       cbn. unfold wproj1.
       f_equal.
       destruct (z == z) eqn:E. rewrite E. done. done. 
       rewrite subst_tm_tm_fresh_eq. auto.
       auto.
     }

  (* result type is well formed. *)
  have BodyWF : forall x, x `notin` dom W \u {{x0}} \u {{y0}} -> 
    Typing ([(x, (q_C, a_WSigma psi0 A B))] ++ meet_ctx_l q_C W) q_C
    (open_tm_wrt_tm
       (close_tm_wrt_tm z (open_tm_wrt_tm B (wproj1 psi0 (a_Var_f z) B)))
       (a_Var_f x)) (a_Type s2).
  { 
    intros x Frx.
    (* simplify type by pushing in subst/open *)
    rewrite <- subst_tm_tm_spec.
    rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc1.
    rewrite (subst_tm_tm_fresh_eq B); auto.
    cbn. rewrite eq_dec_refl. simpl_env. 
    rewrite (subst_tm_tm_fresh_eq B); auto.
    fold (wproj1 psi0 (a_Var_f x) B).

    (* Justify with substitution for proj1 x *)
    pick fresh y.
    have Ux:  uniq ([(x, (q_C, a_WSigma psi0 A B))] ++ meet_ctx_l q_C W).
    { econstructor; try rewrite dom_meet_ctx_l; eauto. }
    have Uyx: uniq ([(y, (q_C, A))] ++ [(x, (q_C, a_WSigma psi0 A B))] ++ meet_ctx_l q_C W).
    { econstructor; eauto.  simpl.  rewrite dom_meet_ctx_l; eauto. }
    have Cx : Ctx ([(x, (q_C, a_WSigma psi0 A B))] ++ meet_ctx_l q_C W).
    { econstructor. eauto using Ctx_meet_ctx_l. simpl_env. eauto. 
      rewrite dom_meet_ctx_l; eauto.  }

    rewrite (subst_tm_tm_intro y); eauto.
    replace (a_Type s2) with (subst_tm_tm (wproj1 psi0 (a_Var_f x) B) y (a_Type s2)). 2: auto.
    eapply Typing_substitution; simpl_env; eauto using Ctx_meet_ctx_l.
    eapply Typing_weakening_middle; eauto. 

    eapply (@Typing_rename_Type x0); eauto. rewrite dom_meet_ctx_l; eauto. 
    econstructor; eauto using Ctx_meet_ctx_l. simpl_env. eauto. rewrite dom_meet_ctx_l; eauto. 

    (* show that proj1 is well typed *)
    eapply T_wproj1 with (x:=x0) (y:= y0).
    + eapply T_Var with (psi0 := q_C); eauto using q_leb_refl. 
    + auto.
    + auto.
    + simpl. rewrite dom_meet_ctx_l; eauto.
    + simpl. rewrite dom_meet_ctx_l; eauto.
    + simpl_env.  simpl_env in H7.
      eapply Typing_weakening_middle; eauto.
      constructor; eauto using Ctx_meet_ctx_l. 
      constructor; eauto using Ctx_meet_ctx_l. 
      rewrite dom_meet_ctx_l; eauto.
  } 
  pick fresh x and apply T_LetPair.
  instantiate (1:= s2). instantiate (1:=B). instantiate (1:=A).
  - eapply BodyWF with (x:=x). auto.
  - (* a is a sigma *) auto.    
  - (* body has right type *) 
    move=> y Fry.
    cbn. simpl_env.

    replace (open_tm_wrt_tm_rec 0 (a_Var_f x) B) with (open_tm_wrt_tm B (a_Var_f x)). 2: auto.
    replace Qualitative_ott.close_tm_wrt_tm with close_tm_wrt_tm. 2: auto.

    (* Result type of body is well formed. *)
    have TBP1: forall w, w `notin` {{x0}} \u {{y0}} \u {{x}} \u fv_tm_tm A \u dom (meet_ctx_l q_C W) ->
      Typing
        ([(w, (q_C, open_tm_wrt_tm B (a_Var_f x)))]
           ++ [(x, (q_C + psi0 * psi, A))] ++ meet_ctx_l q_C W)
        q_C 
        (open_tm_wrt_tm B 
          (a_LetPair psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f w)) 
                     (a_Abs q_Bot B (a_Var_b 1))))
        (a_Type s2).
    { 
      intros w Frw.

      remember (a_LetPair psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f w))
                          (a_Abs q_Bot B (a_Var_b 1))) as a1.

      remember (open_tm_wrt_tm B (a_Var_f x)) as Bx.
      have TBx:  Typing (meet_ctx_l q_C ([(x, (q_C + psi0 * psi, A))] ++ meet_ctx_l q_C W)) q_C Bx (a_Type s2).
      {
        rewrite HeqBx. simpl_env.
        eapply Typing_narrowing with (W1 := [(x, (q_C, A))] ++ meet_ctx_l q_C W).
        2: { econstructor; try rewrite dom_meet_ctx_l; eauto. eapply leq_meet_l. eapply ctx_sub_refl; auto. }
        eapply (@Typing_rename_Type x0).
        auto.
        rewrite dom_meet_ctx_l. auto.
        auto.
        econstructor; eauto using Ctx_meet_ctx_l. simpl_env. eauto.
        rewrite dom_meet_ctx_l. auto.        
      }

      rewrite (subst_tm_tm_intro x0); auto.
      replace (a_Type s2) with (subst_tm_tm a1 x0 (a_Type s2)). 2: auto.

      eapply Typing_weakening_middle with 
        (W := [(w, (q_C, Bx))] ++ [(x, (q_C + psi0 * psi, A))]) in H8.
      2: { simpl. repeat econstructor; try rewrite dom_meet_ctx_l; eauto.  }

      have Tp1 : Typing ([(w, (q_C, Bx))] ++ [(x, (q_C + psi0 * psi, A))] ++ meet_ctx_l q_C W) q_C  a1 A.
      { 
        rewrite Heqa1.
        eapply Typing_narrowing with (W1 := [(w, (q_C, Bx))] ++ [(x, (q_C, A))] ++ meet_ctx_l q_C W).
        2: { econstructor; try rewrite dom_meet_ctx_l; eauto. reflexivity. 
             econstructor; try rewrite dom_meet_ctx_l; eauto. 
             eapply leq_meet_l. eapply ctx_sub_refl; auto. }

        have UU: uniq ([(w, (q_C, Bx))] ++ [(x, (q_C, A))] ++ meet_ctx_l q_C W).
        {  econstructor; auto. econstructor; eauto. rewrite dom_meet_ctx_l. auto. }

        fold (wproj1 psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f w)) B).
        eapply T_wproj1 with (x:=x0)(y:=y0).
        + eapply T_WPair; auto.
          simpl_env. repeat rewrite meet_idem.
          eapply Typing_weakening with (W2 := [(w, (q_C, Bx))] ++ [(x, (q_C, A))]); eauto.
          eapply T_Var with (psi0:= q_C); auto.
          eapply leq_join_r.
          rewrite join_leq; auto. reflexivity.
          rewrite HeqBx.
          eapply T_Var with (psi0:= q_C); auto.
          econstructor; eauto. econstructor; eauto. rewrite dom_meet_ctx_l. auto. reflexivity. reflexivity.
        + auto.
        + econstructor; eauto. econstructor; eauto using Ctx_meet_ctx_l.
        simpl_env; eauto. rewrite dom_meet_ctx_l. auto.
        simpl_env. rewrite meet_idem.
        simpl_env in TBx.
        apply Typing_pumping with (psi1 := q_C) in TBx; try reflexivity.
        rewrite join_leq in TBx.
        eapply leq_meet_l.
        eauto.
        + simpl. rewrite dom_meet_ctx_l. auto.
        + simpl. rewrite dom_meet_ctx_l. auto.
        + simpl_env.
          repeat rewrite meet_idem.
          eapply Typing_weakening_middle with (W:= [(w, (q_C, Bx))] ++ [(x, (q_C, A))]); eauto.
      }

      eapply Typing_substitution; eauto. 
      econstructor; eauto. econstructor; simpl_env; eauto using Ctx_meet_ctx_l.
      rewrite dom_meet_ctx_l. auto.
    } 
      
    pick fresh w and apply T_Abs. 
    ++ 
       have uwl: uniq
                 ([(w, q_C + psi)] ++ [(x, q_C + psi0 * psi)] ++ labels (meet_ctx_l q_C W)).
       { constructor; eauto.
           constructor; eauto.
           simpl_env.  rewrite dom_meet_ctx_l; eauto. 
           simpl_env.  rewrite dom_meet_ctx_l; eauto. }

      rewrite join_leq. apply leq_Bot.
       rewrite <- subst_tm_tm_spec.
       rewrite <- subst_tm_tm_spec.
       rewrite subst_tm_tm_open_tm_wrt_tm; eauto.
       cbn. simpl_env. rewrite eq_dec_refl. 
       rewrite (subst_tm_tm_fresh_eq B). auto.
       rewrite subst_tm_tm_open_tm_wrt_tm; eauto.
       rewrite (subst_tm_tm_fresh_eq B). auto.
       cbn. destruct (x == y) eqn:E2. rewrite E2. subst. clear Fr1 Fr Fr0 H2 H3. fsetdec.
       rewrite E2. rewrite eq_dec_refl. 
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
                      (a_LetPair psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f w)) (a_Abs q_Bot B (a_Var_b 1))).
       { 
         have Fw: x `notin` dom (labels (meet_ctx_l q_C W)). rewrite labels_dom. rewrite dom_meet_ctx_l. auto.
         fresh_apply_Grade xx.
         ++ eapply G_WPair.
         eapply CG_Leq; auto.
         eapply G_Var; auto.
         eapply leq_meet_l.
         eapply G_Var; auto.
         eapply leq_meet_l.
         ++ 
         have uu: uniq
                 ([(xx, psi0)] ++
                               [(w, q_C + psi)] ++ [(x, q_C + psi0 * psi)] ++ labels (meet_ctx_l q_C W)).
         { constructor; eauto.
           simpl_env.  rewrite dom_meet_ctx_l; eauto. }
         cbn. simpl_env.
         fresh_apply_Grade yy.
         cbn. simpl_env.
         eapply G_Var; auto.
         econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
         auto.
         replace (open_tm_wrt_tm_rec 0 (a_Var_f xx) B) with (open_tm_wrt_tm B (a_Var_f xx)). 2: auto.

         destruct (order_q_C_dec q_Top).
         + eapply CG_Leq; auto.
           eapply Grade_weakening_middle with (P3 := [(w, q_C + psi)] ++ [(x, q_C + psi0 * psi)]); auto.
           replace ([(xx, psi0)] ++ labels (meet_ctx_l q_C W)) with (labels (xx ~ (psi0, A) ++ meet_ctx_l q_C W)). 2: { auto. } 
           eapply Typing_Grade with (A := a_Type s2); auto.
           eapply (@Typing_rename_Type x0). auto. rewrite dom_meet_ctx_l. auto.
           2: { econstructor; eauto using Ctx_meet_ctx_l.  simpl_env. eauto.
           rewrite dom_meet_ctx_l; eauto. }
           eapply Typing_narrowing; eauto. econstructor; eauto. eapply ctx_sub_refl. eapply meet_ctx_l_uniq. auto.
         + eapply CG_Nleq.
           move: (Grade_lc GW) => lcb. inversion lcb. eauto.
           eapply lt_not_leq. auto.
           eapply uu.
       } 
       
       have GB: Grade ([(w, q_C + psi)] ++ [(x, q_C + psi0 * psi)] ++ labels (meet_ctx_l q_C W)) q_C
                        (a_App (open_tm_wrt_tm (a_Abs q_Bot B (a_Var_b 1)) (a_Var_f x)) q_Bot (a_Var_f w)). 
       { 
         eapply G_App; auto using leq_Bot.
         + cbn. simpl_env.
           fresh_apply_Grade xx. cbn. simpl_env.
           eapply G_Var; auto.
           econstructor; simpl_env; try rewrite dom_meet_ctx_l; eauto. 
           apply leq_meet_l.
           replace (open_tm_wrt_tm_rec 0 (a_Var_f x) B) with (open_tm_wrt_tm B (a_Var_f x)). 2: auto.
           destruct (order_q_C_dec q_Top).
           ++ eapply CG_Leq; auto.
              eapply Grade_weakening; auto.
              replace ([(x, q_C + psi0 * psi)] ++ labels (meet_ctx_l q_C W)) with (labels (x ~ (q_C + psi0 * psi, A) ++ meet_ctx_l q_C W)). 2: { auto. } 
              eapply Typing_Grade with (A := a_Type s2); auto.
           eapply (@Typing_rename_Type x0). auto. rewrite dom_meet_ctx_l. auto.
           2: { econstructor; eauto using Ctx_meet_ctx_l.  simpl_env. eauto.
           rewrite dom_meet_ctx_l; eauto. }
           eapply Typing_narrowing; eauto. econstructor; eauto. 
           eapply leq_meet_l.
           eapply ctx_sub_refl. eapply meet_ctx_l_uniq. auto.
           ++ eapply CG_Nleq; auto.
               move: (Grade_lc GW) => lcb. inversion lcb. eauto.
              eapply lt_not_leq. auto.
         + eapply CG_Leq; auto.
           eapply leq_Bot.
           eapply G_Var; auto.
           apply leq_meet_l.
       }
       rewrite subst_tm_tm_fresh_eq; auto.
       eapply Eq_Trans.
       eapply Eq_Beta with (b:=  (a_App (open_tm_wrt_tm (a_Abs q_Bot B (a_Var_b 1)) (a_Var_f x)) q_Bot (a_Var_f w))); auto.
       eapply S_LetPairBeta; auto. eapply Grade_lc; eauto.
       eapply Eq_Beta; auto.
       cbn.
       eapply S_Beta.
       move: (Grade_lc GW) => lcb. inversion lcb. eauto.
       eapply (lc_a_Abs_exists x).
       move: (Grade_lc GW) => lcb. inversion lcb. eauto.
       cbn. auto.
       auto.
       eapply G_Var; auto. 
       rewrite meet_mult; auto.
       rewrite join_lub; auto.
       eapply leq_meet_l; auto.
       rewrite subst_tm_tm_fresh_eq. auto.
       eapply Typing_narrowing.
       eapply TBP1.
       rewrite dom_meet_ctx_l; auto.
       repeat econstructor; eauto using ctx_sub_refl, leq_meet_l, q_leb_refl.
       all: simpl; rewrite dom_meet_ctx_l.
       all: auto.
    ++ 
      instantiate (1:= s').
      rewrite <- subst_tm_tm_spec.
      rewrite subst_tm_tm_open_tm_wrt_tm.
      auto.
      rewrite subst_tm_tm_fresh_eq. auto.
      unfold wproj1.
      simpl. rewrite eq_dec_refl. simpl_env.
      rewrite subst_tm_tm_fresh_eq. auto.
      fold (wproj1 psi0 (a_WPair (a_Var_f x) psi0 (a_Var_f y)) B).
      eapply (@rename2 x0 y0).
      auto. auto. auto. auto.
      eauto.
Unshelve. exact q_C.
Qed.
