Require Import ssreflect.
Require Import Coq.Classes.EquivDec.
Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.
Require Import Coq.Classes.RelationClasses.

Require Import dqtt_ott.
Require Import dqtt_inf.
Require Import usage.
Require Import dctx.
Require Import dctx_sub.
Require Import semimodule.
Require Import tactics.

Require Import beta.

(* Stupid structural lemmas from Locally nameless representation *)

Lemma subst_tm_same a x y (E: x = y) : (subst_tm_tm a x (a_Var_f y)) = a.
Proof.
  simpl. subst. rewrite eq_dec_refl. auto.
Qed.

Lemma subst_tm_diff a x y (E: x <> y) : (subst_tm_tm a x (a_Var_f y)) = a_Var_f y.
Proof.
  simpl. destruct (y == x). subst. done. auto.
Qed.

Lemma subst_tm_id :  (forall a x, subst_tm_tm (a_Var_f x) x a = a).
Proof. 
intros. induction a; simpl; auto.
all: try rewrite IHa1.
all: try rewrite IHa2.
all: try rewrite IHa3.
all: try rewrite IHa4.
all: try rewrite IHa.
all: auto.
destruct (x0 == x). subst. auto. auto. 
Qed.


(* Axioms about beta conversion. *)


(* closed under substitution *)


(*******************************************************************)

Lemma Typing_lc1: (forall {D G a A},Typing D G a A -> lc_tm a /\ lc_tm A).
Proof. 
intros. 
induction H.
all: pick fresh z.
all: try match goal with [ H : (forall x, x `notin` ?L -> _) |- _ ] => destruct (H z ltac:(auto)) end.
all: try match goal with [ H : (forall y, y `notin` ?L -> _) |- _ ] => destruct (H z ltac:(auto)) end.
all: repeat  match goal with [ H : _ /\ _ |- _ ] => destruct H end. 
all: split; auto.
all: try (eapply lc_a_Pi_exists with (x1:=z); eauto).
all: try eapply lc_a_Lam_exists with (x1:=z); eauto.
all: try  match goal with [ H4 : lc_tm (a_Pi ?q ?A ?B) |- _ ] => inversion H4; auto end.
all: try solve [rewrite (subst_tm_tm_intro z); auto; eapply subst_tm_tm_lc_tm; eauto].
eapply lc_a_letunitB; auto.
eapply lc_a_Lam_exists with (x1:=z); eauto.
eapply lc_a_LetBoxB_exists with (x1:=z); eauto. eapply H1; auto.
eapply lc_a_Lam_exists with (x1:=z); eauto.
eapply lc_a_Case; auto. 
eapply lc_a_Lam_exists with (x1:=z); eauto.
eapply lc_a_Sigma_exists with (x1:=z); eauto.
eapply lc_a_Sigma_exists with (x1:=z); eauto.
eapply lc_a_Spread_exists with (x1:=z); eauto.
{ pick fresh y. destruct (H2 z ltac:(auto) y ltac:(auto)); auto. }
eapply lc_a_Lam_exists with (x1:=z); eauto.
Qed.

Lemma Typing_lc: forall {D G a A},Typing D G a A -> lc_tm a.
Proof. intros. apply Typing_lc1 in H. destruct H. auto. Qed.

Lemma Typing_lc2: (forall {D G a A},Typing D G a A -> lc_tm A).
Proof. intros. apply Typing_lc1 in H. destruct H. auto. Qed.

Lemma Typing_ctx_fv1 {D G a A} x : Typing D G a A 
                                  -> x `notin` dom D 
                                  -> x `notin` fv_tm_tm a /\ x `notin` fv_tm_tm A.
Proof.
  induction 1; intros; simpl.
  all: repeat match goal with [H : Typing _ _ _ _ |- _] => clear H end.
  all: simpl in *.
  all: repeat match goal with [H : ?x `notin` dom ?D5 -> _ |- _ ] => specialize (H ltac:(auto)) end.
  all: pick fresh y.
  all: have Sx: x `notin` singleton y by auto.
  all: repeat match goal with [H : forall x, x `notin` ?L -> _ -> _ /\ _  |- _ ] => 
           specialize (H y ltac:(auto)) ; simpl in H ; specialize (H ltac:(auto)) ; destruct H end.
  all: repeat match goal with [H : _ /\ _ |- _ ] => destruct H end.
  all: try move: (fv_tm_tm_open_tm_wrt_tm_lower B (a_Var_f y)) => hBy.
  all: try rewrite hBy.
  all: try move: (fv_tm_tm_open_tm_wrt_tm_upper B (a_Var_f y)) => hBy2.
  all: try rewrite hBy2.
  all: try move: (fv_tm_tm_open_tm_wrt_tm_lower a (a_Var_f y)) => ha.
  all: try rewrite ha.
  all: try move: (fv_tm_tm_open_tm_wrt_tm_upper a (a_Var_f y)) => ha2.
  all: try rewrite ha2.
  all: try move: (fv_tm_tm_open_tm_wrt_tm_upper B b) => hBb. 
  all: try rewrite hBb.
  all: try move: (fv_tm_tm_open_tm_wrt_tm_upper B a) => hBa. 
  all: try rewrite hBa.

  all: simpl.
  all: split.
  all: repeat apply notin_union.
  all: eauto 1.
  all: try rewrite hBy; auto 1.
  all: try rewrite <- ha in H0. auto.
  all: try move: (fv_tm_tm_open_tm_wrt_tm_lower b (a_Var_f y)) => hb.
  all: try rewrite hb.
  auto 1.
  pick fresh z.
  move: (H2 y ltac:(auto) z ltac:(auto) ltac:(auto)) => [h2 h3].
  auto 1.
Qed.


Lemma Typing_ctx_fv {D G a A} x : Typing D G a A 
                                  -> x `notin` dom D 
                                  -> x `notin` fv_tm_tm a.
Proof.
intros. eapply Typing_ctx_fv1 in H. destruct H. eauto. eauto.
Qed.

Lemma Typing_ctx_fv2 {D G a A} x : 
  Typing D G a A -> x `notin` dom D -> x `notin` fv_tm_tm A.
Proof.
intros. eapply Typing_ctx_fv1 in H. destruct H. eauto. eauto.
Qed.

Lemma Typing_ctx {D G a A} : Typing D G a A -> ctx D G.
Proof.
  induction 1.
  all: eclarify_ctx.
  all: try solve [eapply ctx_sub_ctx2; eauto].
  all: try solve [pick fresh y0; move: (H0 y0 ltac:(auto)) => h; inversion h; auto].
  all: try solve [pick fresh y0; move: (H1 y0 ltac:(auto)) => h; inversion h; auto].
  pick fresh y0. pick fresh z0. move: (H2 y0 ltac:(auto) z0 ltac:(auto)) => h.
  inversion h; auto.
Qed.


Lemma Typing_uniq1 {D G a A} : Typing D G a A -> uniq D.
Proof.
  intro h. eapply ctx_uniq1. eapply Typing_ctx. eauto.
Qed.


Lemma Typing_uniq2 {D G a A} : Typing D G a A -> uniq G.
Proof.
  intro h. eapply ctx_uniq2. eapply Typing_ctx. eauto.
Qed.



(* ----- substitute into the context ------ *)

Definition subst_D a x := map (subst_tm_sort a x).
Definition subst_G a x := map (fun p : usage * sort => 
                                 match p with
                                 | (q,s) => (q, (subst_tm_sort a x s))
                                 end).

Lemma subst_D_cons a x1 x0 A0 D2 : 
  subst_D a x1 ([(x0, A0)] ++ D2) = (x0 ~ subst_tm_sort a x1 A0) ++ subst_D a x1 D2.
Proof. reflexivity. Qed.
Hint Rewrite subst_D_cons : rewr_list.

Lemma subst_G_cons a x1 x0 A0 G2 q : 
  subst_G a x1 ([(x0, (q, A0))] ++ G2) = (x0 ~ (q,subst_tm_sort a x1 A0))
                                           ++ subst_G a x1 G2.
Proof. reflexivity. Qed.
Hint Rewrite subst_G_cons : rewr_list.

Lemma subst_G_ctx_mul a x q G :
  subst_G a x (ctx_mul q G) = ctx_mul q (subst_G a x G).
Proof. induction G. simpl; auto. simpl. rewrite IHG.
       destruct a0. destruct p. simpl. auto.
Qed.
Hint Rewrite subst_G_ctx_mul : rewr_list.

Lemma subst_G_ctx_plus a x G1 : forall G2,
  subst_G a x (ctx_plus G1 G2) = ctx_plus (subst_G a x G1) (subst_G a x G2).
Proof. induction G1; intro G2. simpl; auto. destruct G2; simpl; auto. 
       simpl. destruct a0. destruct p.
       destruct G2; simpl. auto.
       destruct p. destruct p.
       simpl. rewrite IHG1. auto.
Qed.

Hint Rewrite subst_G_ctx_plus : rewr_list.


Lemma subst_ctx : forall a x D G, 
    ctx D G -> lc_tm a -> ctx (subst_D a x D) (subst_G a x G).
Proof.
  induction 1; asimpl; eauto.
  intros. econstructor; eauto.
  unfold subst_D. rewrite dom_map. auto.
Qed.

Lemma subst_ctx_sub : forall a x D G1 G2, 
    ctx_sub D G1 G2 -> ctx_sub (subst_D a x D) (subst_G a x G1) (subst_G a x G2).
Proof.
  induction 1; asimpl; eauto.
  econstructor; auto.
  unfold subst_D. rewrite dom_map. auto.
Qed.

(* ----------------------------------------------------------------------- *)

(* Add to eclarify_ctx. *)
Ltac typing_ctx ::=
  match goal with 
  | [ |- ctx (subst_D ?a ?x ?D) (subst_G ?a ?x ?G) ] => 
    eapply subst_ctx
  | [ H : Typing ?D ?G ?a ?A |- ctx ?D1 ?G ] => 
    eapply Typing_ctx; eassumption
  | [ |- ctx_sub (subst_D ?a ?x ?D) (subst_G ?a ?x ?G1) (subst_G ?a ?x ?G2) ] =>
    eapply subst_ctx_sub
  end.

(* Find a typing assumption that can set us up for ctx_mid. *)
Ltac ctx_mid_ctx := 
    let CD := fresh in 
    match goal with 
      [ Y : (ctx_plus ?G1 ?G1' ++ ?x ~ (?q, ?A) ++ ctx_plus ?G2 ?G2') = ?G,
        Z : Typing ?D (?G1 ++ ?z ~ (?r, ?A) ++ ?G2) ?a ?B |- _  ] => 
      have CD: (ctx D (ctx_plus G1 G1' ++ x ~ (q, A) ++ ctx_plus G2 G2')) by solve_ctx
(*       try solve_ctx;  ctx_mid; clear CD; clear Y *)
    end.


Lemma Typing_ectx D1 G1 a A D2 G2 
  : Typing D1 G1 a A -> D1 = D2 -> G1 = G2 -> Typing D2 G2 a A.
Proof. intros. subst. auto. Qed.

Lemma Typing_e D G1 a A1 G2 A2 
  : Typing D G1 a A1 -> G1 = G2 -> A1 = A2 -> Typing D G2 a A2.
Proof. intros. subst. auto. Qed.



Lemma cong: forall {A B} (f:A -> B) a b, a = b -> f a = f b. Proof. intros. f_equal. auto. Qed.

(* Theorem 6.2 *)
Lemma substitution D1 D2 G1 G2 x q1 A b B
    (HB:Typing (D2 ++ x ~ Tm A ++ D1) (G2 ++ x ~ (q1, Tm A) ++ G1) b B): 
    forall G a (HA:Typing D1 G a A),
    Typing (subst_D a x D2 ++ D1) 
           (subst_G a x G2 ++ ctx_plus G1 (ctx_mul q1 G)) (subst_tm_tm a x b) 
           (subst_tm_tm a x B).
Proof.
  dependent induction HB; intros.
  - (* sub *)

    repeat destruct_ctx_sub.
    move: (Typing_ctx HA) => CA.
    move: (Typing_ctx HB) => CB.
    move: (ctx_uniq1 CB) => UD. destruct_uniq.
    simpl_env in *.
    
    var_ctx.
    edestruct (@ctx_mid2 sort) as [? [? ?]]; eauto; subst.
    
    eapply T_sub; try eassumption.
    eapply IHHB; try reflexivity; try eassumption.

    eapply ctx_sub_app; auto. eapply subst_ctx_sub; auto.
    eapply ctx_sub_ctx_plus; try eassumption. 
    eapply ctx_sub_ctx_mul; auto.

    unfold subst_D.
    solve_ctx.

  - (* type *)
    simpl in *. simpl_env in *.      
    destruct D2; simpl_env in x1; inversion x1.
  - (* var *)    
    simpl_env in *.
    destruct (x0 == x1).
    ++ (* substituting for this variable. *)
      rewrite subst_tm_same; auto.
      subst.

      move: (Typing_ctx HB) => CB.
      move: (Typing_ctx HA) => CA.

       (* get the contexts in shape *)
       have NG: x1 `notin` dom (ctx_mul 0 G).
       { unfold ctx_mul. 
         rewrite dom_map. 
         erewrite <- ctx_dom; eauto. }
       destruct D2; inversion x2; simpl_env in *; subst.
       2: { simpl_env in H. fsetdec. }
       destruct G2; inversion x; simpl_env in *; subst.
       2: { rewrite H2 in NG. simpl_env in NG. fsetdec. }

       rewrite subst_tm_tm_fresh_eq.
       eapply Typing_ctx_fv; eauto. 

       erewrite (@ctx_ctx_plus_0_l _ _ G G0); eclarify_ctx.

    ++ (* substitute for a different variable *)
       rewrite subst_tm_diff; auto.

       (* get the contexts in shape *)
       destruct D2; inversion x2; simpl_env in *; subst. done.
       destruct G2; inversion x; simpl_env in *; subst. done.
       clear x2. clear x.

       move: (Typing_ctx HA) => CA.
       move: (Typing_ctx HB) => CB.

       have C0: ctx (D2 ++ [(x1, Tm A)] ++ D1) (ctx_mul 0 G). eclarify_ctx.

       destruct_ctx. asimpl in C0. asimpl in H2.
       ctx_mid. clear H2.

       specialize (IHHB _ _ _ _ _ _ _ ltac:(reflexivity)
                                      ltac:(reflexivity) _ _ HA).
       simpl in IHHB.

       simpl_env.
       replace (ctx_mul 0 G0) with (ctx_mul 0 (ctx_mul q G0)).
       erewrite <- ctx_distrib;  try eclarify_ctx.
       erewrite <- ctx_mul_app.
       eapply T_var.
       { unfold subst_D. asimpl. fsetdec. }
       eapply IHHB.
       asimpl. auto.
  - (* weakening case *)
    move: (Typing_ctx HA) => CA.
    move: (Typing_ctx HB1) => CB1.
    move: (Typing_ctx HB2) => CB2.

    destruct D2; inversion x2; simpl_env in *; subst; clear x2;
    destruct G2; inversion x; simpl_env in *; subst; clear x.
    ++  (* substituting for weakened var *)
      repeat rewrite subst_tm_tm_fresh_eq.
      eapply Typing_ctx_fv; eauto.
      eapply Typing_ctx_fv2; eauto.
      erewrite ctx_plus_comm. erewrite ctx_ctx_plus_0_l. auto.
      all: eclarify_ctx.
    ++ (* impossible case *)
      destruct_ctx. simpl_env in H. fsetdec.
    ++ fsetdec.
    ++ (* need to use IH *)
      destruct_ctx.
      specialize (IHHB1 _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA).
      specialize (IHHB2 _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA).
      
      eapply T_weak; eauto.
      { unfold subst_D. asimpl. fsetdec. }

  - (* pi case *)
    simpl.
    move: (Typing_ctx HA) => CA.
    move: (Typing_ctx HB) => CA0.
    destruct_ctx.
    specialize (IHHB _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    simpl in IHHB.


    have C3: ctx (D2 ++ (x0 ~ Tm A) ++ D1) G3.
    { pick fresh z. move: (H z ltac:(auto)) => h.
      move: (Typing_ctx h) => ch. inversion ch. simpl_env in *. auto. }


    simpl_env in x.
    symmetry in x.
    eapply ctx_plus_app_l in x; eclarify_ctx. clear C3.
    move: x => [G4' [G7' [E1 [E2 [C1 C2]]]]].

    inversion C2. subst.
    asimpl in E1.
    
    have CB: ctx (D2 ++ x0 ~ Tm A ++ D1) 
              (ctx_plus G4 G4' ++ x0 ~ (q0 + q2, Tm A) ++ ctx_plus G6 G0). 
           solve_ctx.
    symmetry in E1.
    ctx_mid. clear E1.

    simpl_env.

(* IH for A: Typing (subst_D a x0 D2 ++ D1)
           (subst_G a x0 G4 ++ ctx_plus G6 (ctx_mul q0 G)) 
           (subst_tm a x0 A0) a_Type *)

(* IH for B: 
       Typing ([(y, subst_tm a x0 A0)] ++ subst_D a x0 D2 ++ D1)
         ([(y, (r, subst_tm a x0 A0))] ++
          subst_G a x0 G4' ++ ctx_plus G0 (ctx_mul q2 G))
         (subst_tm a x0 (open_tm_wrt_tm B (a_Var_f y))) a_Type *)

    replace ( ctx_plus (ctx_plus G6 G0) (ctx_mul (q0 + q2) G)) with
        (ctx_plus (ctx_plus G6 (ctx_mul q0 G)) (ctx_plus G0 (ctx_mul q2 G))).
    erewrite <- ctx_plus_app.
    all: eclarify_ctx.

    eapply T_pi with (L := L `union` {{x0}}).
    ++ clear H0. 
       eapply IHHB.
    ++ intros y Fr.
       move: (H y ltac:(fsetdec)) => TA. clear H.
       move: (Typing_ctx TA) => CA0.
       
       simpl_env in *.

       move: (H0 y ltac:(fsetdec) D1 (y ~ Tm A0 ++ D2) G0 (y ~ (r, Tm A0) ++ G4') x0 q2 A ltac:(reflexivity) ltac:(reflexivity) _ _ HA) => TB. clear H0.

      asimpl in TB.
      rewrite subst_tm_tm_open_tm_wrt_tm in TB.
         eapply Typing_lc; eauto.      
      rewrite subst_tm_diff in TB. auto.
      eapply TB.
    ++ eapply subst_ctx; eauto. eapply Typing_lc; eauto.
    ++ eapply subst_ctx; eauto. eapply Typing_lc; eauto.
    ++ erewrite ctx_plus_swap; try eclarify_ctx. 
       f_equal.
       erewrite ctx_distrib2; try eclarify_ctx. auto.
  - (* lam case *)
    (* similar to pi case. *)

    simpl.
    move: (Typing_ctx HA) => CA.
    move: (Typing_ctx HB) => CA0.
    destruct_ctx.
    specialize (IHHB _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    simpl in IHHB.
    eapply T_lam with (L := L `union` {{x}}); eauto.
    intros y Fr.
    move: (H y ltac:(fsetdec)) => TA. clear H.
    move: (Typing_ctx TA) => CA0.
       
    simpl_env in *.

    move: (H0 y ltac:(fsetdec) D1 (y ~ Tm A0 ++ D2) G1 (y ~ (_,Tm A0) ++ _) _ _ A ltac:(reflexivity) ltac:(reflexivity) _ _ HA) => TB. clear H0.

    asimpl in TB.
    rewrite subst_tm_tm_open_tm_wrt_tm in TB.
    eapply Typing_lc; eauto.      
    rewrite subst_tm_tm_open_tm_wrt_tm in TB.
    eapply Typing_lc; eauto.      
    rewrite subst_tm_diff in TB; auto.
  - (* app case *)    
    simpl.
    move: (Typing_ctx HA) => CA.
    move: (Typing_ctx HB1) => CB1.
    move: (Typing_ctx HB2) => CB2.
    have CC: ctx (D2 ++ [(x0, Tm A)] ++ D1) (ctx_plus G0 (ctx_mul q G3)).
    { eclarify_ctx. }
    have CD:  ctx (D2 ++ [(x0, Tm A)] ++ D1) (G2 ++ [(x0, (q1, Tm A))] ++ G1).
    { rewrite x in CC. auto. }
    destruct_ctx.

    asimpl in x.
    erewrite ctx_plus_app in x; try eclarify_ctx. 
    asimpl in x.
    symmetry in x.
    ctx_mid.

    specialize (IHHB1 _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    specialize (IHHB2 _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    simpl in IHHB1.

    move: (T_app _
                 _
                 _
                 _
                 _ _ _ _ IHHB1 IHHB2) => APP.

    rewrite subst_tm_tm_open_tm_wrt_tm. eapply Typing_lc; eauto.

    eapply Typing_ectx; try eapply APP. auto.

    asimpl.
    erewrite ctx_plus_app; try eclarify_ctx.
    2: { apply subst_ctx; eauto; eapply Typing_lc; eauto. }
    2: { apply subst_ctx; eauto; eapply Typing_lc; eauto. }
 
    f_equal.

    erewrite ctx_distrib; try eclarify_ctx. asimpl.
    erewrite ctx_plus_swap; try eclarify_ctx.
    f_equal.
    erewrite ctx_distrib2. eauto.
    all: eclarify_ctx.
  - (* conversion *)
    move: (Typing_ctx HA) => CA.
    move: (Typing_ctx HB1) => CB1.
    move: (Typing_ctx HB2) => CB2.
    var_ctx.
    destruct_ctx.
    asimpl in HB2.

    specialize (IHHB1 _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    specialize (IHHB2 _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 

    move: (T_conv _ _ _ _ _ _ IHHB1 IHHB2) => CONV.

    eapply Typing_ectx. eapply CONV. eapply subst_Beta1.
    eapply Typing_lc; eauto. auto. auto.
    f_equal. 
  - (* Unit type *)
    simpl in *. simpl_env in *.      
    destruct D2; simpl_env in x1; inversion x1.
  - (* Unit term *)
    simpl in *. simpl_env in *.      
    destruct D2; simpl_env in x1; inversion x1.
  - (* let unit *)
    simpl.
    move: (Typing_ctx HB1) => CA1.
    move: (Typing_ctx HB2) => CA2.
    pick fresh z.
    match goal with [ H : forall y, y `notin` ?L -> Typing ?D ?G ?a ?A |- _ ] => 
         move: (Typing_ctx (H z ltac:(auto))) => h1 end. 
    destruct_ctx. clear dependent z. 

    specialize (IHHB1 _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    simpl in IHHB1.
    specialize (IHHB2 _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    simpl in IHHB2.
    rewrite subst_tm_tm_open_tm_wrt_tm in IHHB2; try eapply Typing_lc; eauto.

    eapply Typing_e.
    eapply T_UnitE with (L := L \u {{x0}}) . eauto. eauto.  eauto. eauto.
    move=> y Fry.
    specialize (H1 y ltac:(eauto) D1 (y ~ Tm a_TyUnit ++ D2) G3 (y ~ (r, Tm a_TyUnit) ++ G0) _ _ _  ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    rewrite subst_tm_tm_open_tm_wrt_tm in H1; try eapply Typing_lc. eauto.
    rewrite subst_tm_diff in H1. fsetdec.
    simpl_env in H1.
    eapply H1.
    simpl_env in x.
    erewrite ctx_plus_app in x. erewrite ctx_plus_app in x. simpl in x. simpl_env in x.
    eapply ctx_mid in x.
    move: x => [d1 [d2 d3]]. invert_equality.
    erewrite ctx_plus_app. simpl_env. f_equal.
    erewrite ctx_plus_swap.
    erewrite ctx_distrib2.
    auto.
    all: eclarify_ctx.
    eapply subst_ctx; eclarify_ctx.
    eapply Typing_lc; eauto.
    eapply subst_ctx; eclarify_ctx.
    eapply Typing_lc; eauto.
    solve_uniq.
    rewrite subst_tm_tm_open_tm_wrt_tm. eapply Typing_lc; auto. eauto. auto. 

  - (* Box type *)
    simpl.
    simpl in IHHB.
    eapply T_Box.
    eapply IHHB; eauto.
  - (* box term *)
    simpl.
    simpl in IHHB.
    move: (Typing_ctx HB) => C.
    destruct_ctx. 
    asimpl in x.
    have CD: (ctx (D2 ++ [(x0, Tm A)] ++ D1) (ctx_mul q G3 ++ [(x0, (q * q0, Tm A))] ++ ctx_mul q G5)). solve_ctx.
    ctx_mid. clear x.
    asimpl.
    rewrite <- ctx_mul_assoc.
    erewrite <- ctx_distrib; eclarify_ctx.
    rewrite <- ctx_mul_app.
    eapply T_box.
    eauto.
  - (* let unbox term *)
    simpl.
    move: (Typing_ctx HA) => CA.
    move: (Typing_ctx HB) => CB1.

    pick fresh z.
    move: (H z ltac:(auto)) => h.
    move: (Typing_ctx h) => h1. clear h.
    move: (H1 z ltac:(auto)) => h2.
    move: (Typing_ctx h2) => h3. clear h2.

    destruct_ctx.

    specialize (IHHB _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    simpl in IHHB.

    asimpl in x.
    erewrite ctx_plus_app in x; eclarify_ctx.
    erewrite ctx_plus_app in x; eclarify_ctx.
    asimpl in x.

    asimpl in HB.

    ctx_mid_ctx.
    ctx_mid.

    eapply Typing_e.
    eapply T_letbox with (L := L \u  {{x0}} \u {{z}}).
    eauto.
    {
      intros y1 Fry.
      have FF: y1 `notin` L. fsetdec.
      move: (H y1 FF) => TA. clear H.
      move: (Typing_ctx TA) => CA0.
       
      simpl_env in *.
      destruct_ctx.

      (* Induction hypotheses *)
      specialize (H0 y1 ltac:(auto) D1 ([(y1, Tm A0)] ++ D2)).
      specialize (H0 G8 ([(y1, (q, Tm A0))] ++ G0)).
      specialize (H0 x0 q3 A ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
      asimpl in H0.


      rewrite subst_tm_tm_open_tm_wrt_tm in H0. eapply Typing_lc; eauto.
      rewrite subst_tm_tm_open_tm_wrt_tm in H0. eapply Typing_lc; eauto.
      rewrite subst_tm_diff in H0. clear -Fry. fsetdec.
      replace (subst_tm_tm a0 x0 (a_box q (a_Var_f y1))) with
          (a_box q (subst_tm_tm a0 x0 (a_Var_f y1))) in H0.
      rewrite subst_tm_diff in H0. clear -Fry. fsetdec.
      asimpl in H0.
      eapply H0.
      reflexivity.
    }
    {
      intros y1 Fry.
      have FF: y1 `notin` L. fsetdec.
      specialize (H2 y1 ltac:(auto) D1 ([(y1, Tm (a_Box q A0))] ++ D2)).
      specialize (H2 G3 ([(y1, (r, Tm (a_Box q A0)))] ++ G4)).
      specialize (H2 x0 q2 A ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
      asimpl in H2. 
      rewrite subst_tm_tm_open_tm_wrt_tm in H2. eapply Typing_lc; eauto.
      rewrite subst_tm_diff in H2. clear -Fry. fsetdec.
      eapply H2. 
    }
    { erewrite subst_G_ctx_plus.
      erewrite ctx_plus_app. f_equal.
      erewrite ctx_plus_swap.
      f_equal.
      erewrite ctx_distrib2. auto. 
      all: eclarify_ctx.
      eapply subst_ctx; eauto. eapply Typing_lc; eauto.
      eapply subst_ctx; eauto. eapply Typing_lc; eauto.
    }
    rewrite subst_tm_tm_open_tm_wrt_tm. eapply Typing_lc; eauto. auto.
  - (* sum type *)
    move: (Typing_ctx HB1) => CA.
    move: (Typing_ctx HB2) => CB1.
    destruct_ctx.
    simpl_env in *.
    simpl.
    eapply Typing_e.
    eapply T_sum.
    eapply IHHB1; eauto.
    eapply IHHB2; eauto.
    
    asimpl in x.
    erewrite ctx_plus_app in x; try eclarify_ctx. 
    asimpl in x.
    eapply ctx_mid in x.
    destruct x as [h1 [h2 h3]].
    invert_equality.
    repeat erewrite ctx_plus_app; eclarify_ctx.
    erewrite subst_G_ctx_plus.
    f_equal.
    erewrite ctx_plus_swap.
    f_equal.
    erewrite ctx_distrib2. auto. 
    all: eclarify_ctx.
    eapply subst_ctx; eauto. eapply Typing_lc; eauto.
    eapply subst_ctx; eauto. eapply Typing_lc; eauto.
    solve_uniq.
    auto.
  - move: (Typing_ctx HB1) => CA.
    move: (Typing_ctx HB2) => CA2.
    destruct_ctx.
    simpl.
    eapply T_inj1; eauto.
    eapply IHHB2; simpl_env; eauto.
  - move: (Typing_ctx HB1) => CA.
    move: (Typing_ctx HB2) => CA2.
    destruct_ctx.
    simpl.
    eapply T_inj2; eauto.
    eapply IHHB2; simpl_env; eauto.
  - (* case *)
    move: (Typing_ctx HB1) => C1.
    move: (Typing_ctx HB2) => C2.
    move: (Typing_ctx HB3) => C3.
    pick fresh z. 
    match goal with [ H : forall y, y `notin` ?L -> Typing ?D ?G ?a ?A |- _ ] => 
         move: (Typing_ctx (H z ltac:(auto))) => h1 end. 
    destruct_ctx. clear dependent z. 

    simpl in *.
    have LC: lc_tm a0. eapply Typing_lc; eauto.
    eapply Typing_e.
    eapply T_case with (L := L \u dom D1 \u dom D2 \u  {{x0 }} ) (B1:=(subst_tm_tm a0 x0 B1))(B2:=(subst_tm_tm a0 x0 B2)) ; auto.
    + eapply IHHB1; try reflexivity. eauto.
    + move=> x1 Fr. 
      repeat match goal with [ H : forall y, y `notin` L ->  _ |- _ ] => specialize (H x1 ltac:(auto)) end.
      match goal with [ H0 : open_tm_wrt_tm B1 (a_Var_f ?x1) = open_tm_wrt_tm ?B (a_Inj1 (a_Var_f ?x1)) |- _ ] => 
         apply (cong(subst_tm_tm a0 x0)) in H0;
         repeat rewrite subst_tm_tm_open_tm_wrt_tm in H0; auto;
         simpl in H0; destruct (x1 == x0) eqn:EQ ; rewrite EQ in H0; subst; try fsetdec ; eapply H0
      end.
    + move=> x1 Fr. 
      repeat match goal with [ H : forall y, y `notin` L ->  _ |- _ ] => specialize (H x1 ltac:(auto)) end.
      match goal with [ H0 : open_tm_wrt_tm B2 (a_Var_f ?x1) = open_tm_wrt_tm ?B (a_Inj2 (a_Var_f ?x1)) |- _ ] => 
         apply (cong(subst_tm_tm a0 x0)) in H0;
         repeat rewrite subst_tm_tm_open_tm_wrt_tm in H0; auto;
         simpl in H0; destruct (x1 == x0) eqn:EQ ; rewrite EQ in H0; subst; try fsetdec ; eapply H0
      end.
    + eapply IHHB2; try reflexivity. eauto.
    + eapply IHHB3; try reflexivity. eauto.
    + clear IHHB1 IHHB2 IHHB3. move=> x1 Fr.
      repeat match goal with [ H : forall y, y `notin` L ->  _ |- _ ] => specialize (H x1 ltac:(auto)) end.
      match goal with [H3 : forall D3 D4, _ |- _ ] => 
         specialize (H3 D1 (x1 ~ Tm (a_Sum A1 A2) ++ D2) G3 (x1 ~ (r, Tm (a_Sum A1 A2)) ++ G0));
           specialize (H3 _ _ _ ltac:(reflexivity) ltac:(reflexivity));
           specialize (H3 _ _ HA);
           simpl_env in H3;
           rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto using Typing_lc;
             rewrite subst_tm_diff in H3; auto; 
           eapply H3
      end. 
    + asimpl in x.
      erewrite ctx_plus_app in x; try eclarify_ctx. 
      asimpl in x.
      eapply ctx_mid in x.
      destruct x as [h1 [h2 h3]].
      invert_equality.
      simpl_env.
      repeat erewrite ctx_plus_app; eclarify_ctx.
      f_equal.
      erewrite ctx_distrib.
      erewrite ctx_plus_swap.
      simpl_env.
      f_equal.
      erewrite ctx_distrib2.
      auto.
      all: eclarify_ctx.
      eapply subst_ctx; eclarify_ctx.
      eapply subst_ctx; eclarify_ctx.
      solve_uniq.
    + rewrite subst_tm_tm_open_tm_wrt_tm; auto.
  - (* Sigma case *)
    simpl.
    move: (Typing_ctx HA) => CA.
    move: (Typing_ctx HB) => CA0.
    destruct_ctx.
    specialize (IHHB _ _ _ _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ HA). 
    simpl in IHHB.


    have C3: ctx (D2 ++ (x0 ~ Tm A) ++ D1) G3.
    { pick fresh z. move: (H z ltac:(auto)) => h.
      move: (Typing_ctx h) => ch. inversion ch. simpl_env in *. auto. }


    simpl_env in x.
    symmetry in x.
    eapply ctx_plus_app_l in x; eclarify_ctx. clear C3.
    move: x => [G4' [G7' [E1 [E2 [C1 C2]]]]].

    inversion C2. subst.
    asimpl in E1.
    
    have CB: ctx (D2 ++ x0 ~ Tm A ++ D1) 
              (ctx_plus G4 G4' ++ x0 ~ (q0 + q2, Tm A) ++ ctx_plus G6 G0). 
           solve_ctx.
    symmetry in E1.
    ctx_mid. clear E1.

    simpl_env.

    replace ( ctx_plus (ctx_plus G6 G0) (ctx_mul (q0 + q2) G)) with
        (ctx_plus (ctx_plus G6 (ctx_mul q0 G)) (ctx_plus G0 (ctx_mul q2 G))).
    erewrite <- ctx_plus_app.
    all: eclarify_ctx.

    eapply T_Sigma with (L := L `union` {{x0}}).
    ++ clear H0. 
       eapply IHHB.
    ++ intros y Fr.
       move: (H y ltac:(fsetdec)) => TA. clear H.
       move: (Typing_ctx TA) => CA0.
       
       simpl_env in *.

       move: (H0 y ltac:(fsetdec) D1 (y ~ Tm A0 ++ D2) G0 (y ~ (r, Tm A0) ++ G4') x0 q2 A ltac:(reflexivity) ltac:(reflexivity) _ _ HA) => TB. clear H0.

      asimpl in TB.
      rewrite subst_tm_tm_open_tm_wrt_tm in TB.
         eapply Typing_lc; eauto.      
      rewrite subst_tm_diff in TB. auto.
      eapply TB.
    ++ eapply subst_ctx; eauto. eapply Typing_lc; eauto.
    ++ eapply subst_ctx; eauto. eapply Typing_lc; eauto.
    ++ erewrite ctx_plus_swap; try eclarify_ctx. 
       f_equal.
       erewrite ctx_distrib2; try eclarify_ctx. auto.
  - (* tensor *)
    move: (Typing_ctx HB1) => C1.
    move: (Typing_ctx HB2) => C2.
    pick fresh z. 
    match goal with [ H : forall y, y `notin` ?L -> Typing ?D ?G ?a ?A |- _ ] => 
         move: (Typing_ctx (H z ltac:(auto))) => h1 end. 
    destruct_ctx. clear dependent z. 

    simpl_env in x.
    erewrite ctx_plus_app in x; eclarify_ctx. 2: { solve_uniq. }
    asimpl in x.
    eapply ctx_mid in x. 2: { eclarify_ctx. solve_uniq. }
    destruct x as [h1 [h2 h3]].
    invert_equality.

    simpl.
    eapply Typing_e.
    eapply T_Tensor with (L := L \u dom D1 \u {{x0}} \u dom D2) (r:=r) (G3:=subst_G a0 x0 G0 ++ ctx_plus G3 (ctx_mul q3 G)); auto.
    + eapply IHHB1; simpl_env; eauto.
    + eapply Typing_e.
      eapply IHHB2; simpl_env; eauto.
      eauto.
      rewrite subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc.
    + move=> y Fr.

      move: (H0 y ltac:(auto)) => h.
      specialize (h _ (y ~ Tm _ ++ _) _ (y ~ (_, Tm _) ++ _) _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      specialize (h _ _ HA).
      simpl in h.
      simpl_env in h.
      rewrite (subst_tm_tm_open_tm_wrt_tm B)  in h; eauto using Typing_lc.
      simpl in h. simpl_env in h. 
      destruct (y == x0) eqn:E; try rewrite E in h. subst. fsetdec. clear E. 
      eapply h.
    + instantiate (1 := q).
      asimpl; eclarify_ctx.
      repeat erewrite ctx_plus_app; eclarify_ctx.
      f_equal.
      erewrite ctx_distrib.
      erewrite ctx_plus_swap.
      simpl_env.
      f_equal.
      erewrite ctx_distrib2.
      auto.
      all: eclarify_ctx.
      eapply subst_ctx; eclarify_ctx.
      eauto using Typing_lc.
      eapply subst_ctx; eclarify_ctx.
      eauto using Typing_lc.
    + eauto.
  - (* spread *)
    move: (Typing_ctx HB) => C1.
    pick fresh z. 
    pick fresh w.
    match goal with [ H : forall x, x `notin` ?L -> forall y, y `notin` ?L2 -> 
                                                   Typing ?D ?G (open_tm_wrt_tm b _) ?A |- _ ] => 
         move: (Typing_ctx (H z ltac:(auto) w ltac:(auto))) => C2 end. 
    match goal with [ H : forall y, y `notin` ?L -> Typing ?D ?G (open_tm_wrt_tm B _) ?A  |- _ ] => 
         move: (Typing_ctx (H z ltac:(auto))) => C3 end. 
    destruct_ctx. clear dependent z. clear dependent w.

    simpl.
    eapply Typing_e.
    eapply T_Spread with (L := L \u dom D1 \u {{x0}} \u dom D2 \u fv_tm_tm a0)
                         (G2 := subst_G a0 x0 G0 ++ ctx_plus G8 (ctx_mul q3 G))
                         (G3 := subst_G a0 x0 G4 ++ ctx_plus G3 (ctx_mul q2 G)).
    6: { rewrite <- subst_tm_tm_open_tm_wrt_tm; eauto using Typing_lc. }

    + eauto.
    + eapply IHHB; simpl_env; eauto.
    + move=> y Fr.
      move=> w Frw.
      move: (H1 y ltac:(auto) w ltac:(auto)) => h.
      specialize (h _ (y ~ Tm _ ++ _) _ (y ~ (_, Tm _) ++ _) _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      specialize (h _ _ HA).
      simpl in h.
      simpl_env in h.
      rewrite (subst_tm_tm_open_tm_wrt_tm b) in h; eauto using Typing_lc.
      rewrite (subst_tm_tm_open_tm_wrt_tm A2) in h; eauto using Typing_lc.
      rewrite subst_tm_tm_close_tm_wrt_tm  in h; eauto using Typing_lc.
      rewrite (subst_tm_tm_open_tm_wrt_tm B) in h; eauto using Typing_lc.
      simpl in h. simpl_env in h. 
      destruct (y == x0) eqn:E; try rewrite E in h. subst. fsetdec. clear E.
      destruct (w == x0) eqn:E; try rewrite E in h. subst. fsetdec. clear E.
      eapply h.
    + move=> y Fr.
      move: (H3 y ltac:(auto)) => h.
      specialize (h _ (y ~ Tm _ ++ _) _ (y ~ (_, Tm _) ++ _) _ _ _ ltac:(reflexivity) ltac:(reflexivity)).
      specialize (h _ _ HA).
      simpl in h.
      simpl_env in h.
      rewrite (subst_tm_tm_open_tm_wrt_tm B)  in h; eauto using Typing_lc.
      simpl in h. simpl_env in h. 
      destruct (y == x0) eqn:E; try rewrite E in h. subst. fsetdec. clear E. 
      eapply h.
    + simpl_env in x.
      erewrite ctx_plus_app in x; eclarify_ctx.
      asimpl in x.
      eapply ctx_mid in x.
      destruct x as [h1 [h2 h3]].
      invert_equality.
      simpl_env.
      repeat erewrite ctx_plus_app; eclarify_ctx.
      f_equal.
      erewrite ctx_plus_swap.
      simpl_env.
      f_equal.
      erewrite ctx_distrib2.
      auto.
      all: eclarify_ctx.
      eapply subst_ctx; eclarify_ctx.
      eauto using Typing_lc.
      eapply subst_ctx; eclarify_ctx.
      eauto using Typing_lc.
      solve_uniq.
Qed.



(* Lemma 6.3 *)
Lemma weakening : forall D1 G1 D2 G2 a A x B G3,
  Typing (D1 ++ D2) (G1 ++ G2) a A ->
  ctx (D1 ++ x ~ Tm B ++ D2) (G1 ++ x ~ (0,Tm B) ++ G2) ->
  Typing D2 G3 B a_Type ->
  Typing (D1 ++ x ~ Tm B ++ D2) (G1 ++ x ~ (0,Tm B) ++ G2) a A.
Proof.
  intros. move: x B G3 H0 H1.
  dependent induction H; intros.
  - move: (Typing_ctx H) => CH.
    move: (ctx_uniq1 H1) => u1.
    var_ctx.
    destruct_ctx.
    eapply split_ctx_sub in H0; eclarify_ctx. destruct H0.
    eapply T_sub.
    + eapply IHTyping; eauto. solve_ctx. 
    + eapply ctx_sub_app; eauto.
      eapply ctx_sub_app; eauto.
      econstructor; eauto. reflexivity.
  - (* type *)
    destruct G1; inversion x. destruct G2; inversion x. simpl_env in *.
    destruct D1; inversion x0. destruct D2; inversion x0. simpl_env in *.
    invert_ctx.
    eapply T_weak; eauto.
  - (* var *)
    var_ctx. clear H1.
    (* check to see whether first var in ctx is weakened var or this var *)
    destruct D1; inversion VarCtx0; subst; clear VarCtx0.
    + (* weakened var *)
      simpl_env in *. subst.
      eapply T_weak. auto.
      eapply T_var; eauto. 
      eauto.
    + (* this var *)
      simpl_env in *.
      invert_equality.

      (* deconstruct the rest of the context *)
      match goal with 
        [ H9 : ctx_mul 0 ?G0 = ?G ++ ?G2 |- _ ] => 
          move: (ctx_mul_0_eq _ H9) => h ;
          simpl_env in h; rewrite <- h in H9 ;
          eapply split_app in h; 
          first (move: h => [h0 h1];
            move: (ctx_mul_app_split _ _ _ _ _ H9) => [G' [G2' [e1 [e2 e3]]]]);
          try eclarify_ctx
      end.

      eapply Typing_ectx. 
      eapply T_var with (D5 := D1 ++ x2 ~ Tm B ++ D2)(G := G' ++ x2 ~ (0, Tm B) ++ G2'); auto.
      ++ eapply IHTyping; eauto. 
         rewrite e1; reflexivity.
         have C1: ctx D1 (ctx_mul 0 G0). eclarify_ctx. 
           rewrite e2 in C1.
         have C2: ctx D2 (ctx_mul 0 G2). eclarify_ctx.
           rewrite e3 in C2.
         eclarify_ctx. fsetdec. solve_uniq.
      ++ eauto. 
      ++ simpl_env. repeat f_equal. congruence.
           simpl. ring_equal. auto. congruence. 
  - (* weak *)
    var_ctx.
    destruct D1; inversion VarCtx0. 
    + simpl_env in *. subst.
      inversion VarCtx1. subst. 
      simpl_env in *. inversion x. subst.
      eapply T_weak; eauto.
    + subst. simpl_env in *.
      invert_equality.
      move: (Typing_ctx H1) => h.
      destruct_ctx.
      eapply T_weak; eauto.
      eapply IHTyping2; eauto.
      solve_ctx.
  - (* Pi *)
    var_ctx.
    symmetry in x.
    eapply ctx_plus_app_result in x.
    all: eclarify_ctx.
    destruct x as [G01 [G02 [G11 [G12 [h0 [h1 [h2 [h3 [h4 [h5 [h6 h7]]]]]]]]]]].
    subst.
    eapply Typing_e.
    eapply T_pi with (L := L \u {{x0}} \u dom D1 \u dom D2).
    eapply IHTyping; eauto.
    eclarify_ctx. fsetdec.
    solve_uniq.
    move=> y Fr.
    specialize (H1 y ltac:(auto) (y ~ Tm A ++ D1) (y ~ (r, Tm A) ++ G11)).
    eapply H1; simpl_env; eauto.
    eclarify_ctx. fsetdec. solve_uniq. solve_uniq.
    erewrite ctx_plus_app; eclarify_ctx; auto.
    f_equal.
    erewrite ctx_plus_app; eclarify_ctx; auto.
    simpl. ring_equal. auto.
    pick fresh y.
    specialize (H0 y ltac:(auto)).
    move: (Typing_ctx H0) => h. inversion h.
    auto.
  - (* lam *)
    var_ctx.
    move: (Typing_ctx H1) => h.
    destruct_ctx.
    eapply Typing_e.
    eapply T_lam with  (L := L \u {{x}} \u dom D1 \u dom D2).
    + move=> x0 Fr.
      specialize (H0 x0 ltac:(auto) ((x0 ~ Tm A) ++ D1)(x0 ~ (q, Tm A) ++ G1)).
      eapply H0; simpl_env; auto.
      eauto.
    + eapply IHTyping; eauto. eclarify_ctx. fsetdec. solve_uniq.
    + simpl. auto.
    + auto.
  - (* app *)
    move: (Typing_ctx H) => h.
    move: (Typing_ctx H0) => h0.
    destruct_ctx.
    var_ctx.
    eapply Typing_e.
    eapply T_app.
    + eapply IHTyping1; eauto. solve_ctx. 
    + eapply IHTyping2; eauto. solve_ctx.
    + simpl_env. erewrite ctx_plus_app; eclarify_ctx. 
      erewrite ctx_plus_app; eclarify_ctx. simpl; simpl_env.
      simpl_env in x. erewrite ctx_plus_app in x; eclarify_ctx.
      eapply split_app in x; eclarify_ctx. move: x => [e1 e2].
      rewrite e1. rewrite e2. ring_simpl. reflexivity.
      all: try fsetdec.
    + auto.
  - (* conv *)
    var_ctx.
    move: (Typing_ctx H0) => h0.
    destruct_ctx.    
    eapply T_conv.
    eapply IHTyping1; eauto.
    eapply IHTyping2; eauto.
    solve_ctx.
    auto.
  - (* unit *)
    destruct D1; destruct D2; inversion x0.
    destruct G1; destruct G2; inversion x.
    simpl_env.
    eapply T_weak; eauto.
  - (* Unit *)
    destruct D1; destruct D2; inversion x0.
    destruct G1; destruct G2; inversion x.
    simpl_env.
    eapply T_weak; eauto.
  - (* let unit *)
    var_ctx.
    move: (Typing_ctx H) => h.
    move: (Typing_ctx H1) => h0.
    move: (Typing_ctx H4) => C4.
    pick fresh z. move: (H2 z ltac:(auto)) => TC. move: (Typing_ctx TC) => C5.
    destruct_ctx.
    erewrite ctx_plus_app in x; eclarify_ctx.
    eapply split_app in x; eclarify_ctx. move: x => [e1 e2].

    eapply Typing_e.
    eapply T_UnitE with (L := L \u {{x0}} \u dom D1 \u dom D2).
    eapply IHTyping1; eauto. solve_ctx.
    eauto.
    eapply IHTyping2; eauto. solve_ctx.
    3: auto.
    2: {
      erewrite ctx_plus_app; eclarify_ctx.
      erewrite ctx_plus_app; eclarify_ctx.
      simpl. simpl_env. ring_simpl.
      repeat f_equal; auto.
      all: try solve_uniq.
    }
    1: {
      move=> y Fry.
      eapply Typing_ectx. 
      eapply H3 with (D3 := ((y ~ Tm a_TyUnit)++D1)) (G1 := [(y, (r, Tm a_TyUnit))]++G0). auto.
      simpl_env. eauto.
      simpl_env. eauto.
      eclarify_ctx.
      eauto.
      instantiate (1 := x0). eauto.
      solve_uniq.
      eauto.
      simpl_env. eauto. 
      simpl_env. eauto.
    }
  - (* box type *)
    var_ctx.
    eapply T_Box.
    eapply IHTyping; eauto.
  - (* box term *)
    var_ctx.
    move: (Typing_ctx H) => h.
    destruct_ctx.
    eapply Typing_e.
    eapply T_box.
    eapply IHTyping; eauto.
    3: { eauto. }
    solve_ctx.
    simpl_env.
    simpl_env in x.
    eapply split_app in x; eclarify_ctx. destruct x.
    repeat f_equal; auto.
    asimpl. auto.
  - (* unbox *)
    var_ctx.
    move: (Typing_ctx H) => h.
    pick fresh y.
    move: (Typing_ctx (H0 y ltac:(auto))) => h0.
    move: (Typing_ctx (H2 y ltac:(auto))) => h1.  clear Fr.
    destruct_ctx.
   
    eapply Typing_e.
    eapply T_letbox with (L := L \u dom D1 \u {{x0}} \u dom D2).
    + eapply IHTyping; eauto. solve_ctx. 
    + move=> z Frz.
      eapply Typing_ectx.
      eapply H1 with (D3 := z ~ Tm A ++ D1) (G1:=(z ~  (q,Tm A) ++ G0)); simpl_env; eauto.
      solve_ctx.
      reflexivity.
      reflexivity.
    + move=> z Frz.
      eapply Typing_ectx.
      eapply H3 with (D3 := z ~ Tm (a_Box q A) ++ D1) (G1:=(z ~  (r,Tm (a_Box q A)) ++ G4)); simpl_env; eauto.
      solve_ctx.
      reflexivity.
      reflexivity.
    + erewrite ctx_plus_app; eclarify_ctx.
      erewrite ctx_plus_app; eclarify_ctx.
      asimpl. 
      erewrite ctx_plus_app in x; eclarify_ctx.
      eapply split_app in x; eclarify_ctx. destruct x.
      repeat f_equal. auto. auto.
      all: solve_uniq.
    + auto.
  - (* sum *)
    var_ctx.
    move: (Typing_ctx H) => C1.
    move: (Typing_ctx H0) => C2.
    destruct_ctx.
    eapply Typing_e.
    eapply T_sum.
    eapply IHTyping1; eauto.
    eclarify_ctx. auto. solve_uniq.
    eapply IHTyping2; eauto.
    eclarify_ctx. auto. solve_uniq.

    erewrite ctx_plus_app; eclarify_ctx; auto.
    erewrite ctx_plus_app; eclarify_ctx; auto.
    asimpl. 
    erewrite ctx_plus_app in x; eclarify_ctx.
    eapply split_app in x; eclarify_ctx. destruct x.
    repeat f_equal. auto. auto.
    auto.
  - (* inl *)
    move: (Typing_ctx H0) => C1.
    var_ctx.
    destruct_ctx.
    eapply T_inj1; eauto.
    eapply IHTyping2; eauto.
    eclarify_ctx. auto. solve_uniq.
  - (* inj2 *)
    move: (Typing_ctx H0) => C1.
    var_ctx.
    destruct_ctx.
    eapply T_inj2; eauto.
    eapply IHTyping2; eauto.
    eclarify_ctx. auto. solve_uniq.
  - (* case *)
    var_ctx.
    match goal with [H : Typing _ _ a _ |- _ ] => move: (Typing_ctx H) => C1 end.
    match goal with [H : Typing _ _ b1 _ |- _ ] => move: (Typing_ctx H) => C2 end.
    match goal with [H : Typing _ _ b2 _ |- _ ] => move: (Typing_ctx H) => C3 end.
    match goal with [H : forall y, y `notin` ?L -> Typing _ _ _ _ |- _ ] => 
       pick fresh z; move: (H z ltac:(auto)) => h; move: (Typing_ctx h) => C4    
end.                                                                           
    destruct_ctx. clear dependent z.

    eapply Typing_e.
    eapply T_case with (L := L \u dom D1 \u {{x0}} \u dom D2); auto.
    + eapply IHTyping1; eauto.
      eclarify_ctx. fsetdec. solve_uniq.
    + eapply IHTyping2; eauto.
      eclarify_ctx. fsetdec. solve_uniq.
    + eapply IHTyping3; eauto.
      eclarify_ctx. fsetdec. solve_uniq.
    + move=> y Fr.
      eapply Typing_ectx.
      match goal with [H6 : forall y, y `notin` ?L -> forall D3, _ |- _ ] => 
          eapply (H6 y ltac:(fsetdec) _ _) end.  4 : { eauto. }
      rewrite <- app_assoc. eauto.
      3: {  simpl_env.  eauto. }
      2: { eclarify_ctx. econstructor. eauto. auto. auto. solve_uniq. }
      simpl_env. eauto.
      simpl_env. eauto.
    + simpl_env.
      erewrite ctx_plus_app; eclarify_ctx; auto.
      erewrite ctx_plus_app; eclarify_ctx; auto.
      asimpl. 
      asimpl in x. erewrite ctx_plus_app in x; eclarify_ctx.
      eapply split_app in x; eclarify_ctx. destruct x.
      repeat f_equal. auto. auto.
    + auto.
  - (* Sigma *)
    var_ctx.
    symmetry in x.
    eapply ctx_plus_app_result in x.
    all: eclarify_ctx.
    destruct x as [G01 [G02 [G11 [G12 [h0 [h1 [h2 [h3 [h4 [h5 [h6 h7]]]]]]]]]]].
    subst.
    eapply Typing_e.
    eapply T_Sigma with (L := L \u {{x0}} \u dom D1 \u dom D2).
    eapply IHTyping; eauto.
    eclarify_ctx. fsetdec.
    solve_uniq.
    move=> y Fr.
    specialize (H1 y ltac:(auto) (y ~ Tm A ++ D1) (y ~ (r, Tm A) ++ G11)).
    eapply H1; simpl_env; eauto.
    eclarify_ctx. fsetdec. solve_uniq. solve_uniq.
    erewrite ctx_plus_app; eclarify_ctx; auto.
    f_equal.
    erewrite ctx_plus_app; eclarify_ctx; auto.
    simpl. ring_equal. auto.
    pick fresh y.
    specialize (H0 y ltac:(auto)).
    move: (Typing_ctx H0) => h. inversion h.
    auto.
  - (* tensor *)
    var_ctx.
    match goal with [H : Typing _ _ a _ |- _ ] => move: (Typing_ctx H) => C1 end.
    match goal with [H : Typing _ _ b _ |- _ ] => move: (Typing_ctx H) => C2 end.
    match goal with [H : forall y, y `notin` ?L -> Typing _ _ (_ B _) _ |- _ ] => 
       pick fresh z; move: (H z ltac:(auto)) => h; move: (Typing_ctx h) => C4    
end.                                                                           
    destruct_ctx. clear dependent z.

    eapply Typing_e.
    eapply T_Tensor with (L := L \u dom D1 \u {{x0}} \u dom D2); auto.
    5: { eauto. }
    + eapply IHTyping1; eauto.
      eclarify_ctx. fsetdec. solve_uniq.
    + eapply IHTyping2; eauto.
      eclarify_ctx. fsetdec. solve_uniq.
    + move=> y Fr.
      eapply (H2 y ltac:(fsetdec) (y ~ _ ++ _) (y ~ _ ++ G0) D2 G8); simpl_env; eauto.
      eclarify_ctx. fsetdec. solve_uniq.
      simpl_env. eauto.
    + asimpl.
      erewrite ctx_plus_app; eclarify_ctx; auto.
      erewrite ctx_plus_app; eclarify_ctx; auto.
      asimpl. 
      asimpl in x. erewrite ctx_plus_app in x; eclarify_ctx.
      eapply split_app in x; eclarify_ctx. destruct x.
      repeat f_equal. auto. auto.
  - (* spread *)
    var_ctx.
    match goal with [H : Typing _ _ a _ |- _ ] => move: (Typing_ctx H) => C1 end.
    pick fresh z. pick fresh w.
    match goal with [H : forall y, y `notin` ?L -> Typing _ _ (_ B _) _ |- _ ] => 
       move: (H z ltac:(auto)) => h4; 
       move: (Typing_ctx h4) => C4 end.
    match goal with [H : forall x, x `notin` ?L -> forall y, y `notin` ?L2 -> Typing _ _ (_ b _) _ |- _ ] => 
       move: (H z ltac:(auto) w ltac:(auto)) => h2;
       move: (Typing_ctx h2) => C2 end.
    destruct_ctx. clear dependent z. clear dependent w.

    eapply Typing_e.
    eapply T_Spread with (L := L \u dom D1 \u {{x0}} \u dom D2); auto.
    5: { reflexivity. }
    + eapply IHTyping; eauto.
      eclarify_ctx. fsetdec. solve_uniq.
    + move=> y Fr. move=> w Frw.
      eapply (H2 y ltac:(auto) w ltac:(auto) (y ~ _ ++ _) (y ~ _ ++ G3) _ G8); simpl_env; eauto.
      eclarify_ctx. solve_uniq. solve_uniq. simpl_env. solve_notin.
    + move=> y Fr.
      eapply (H4 y ltac:(auto) (y ~ _ ++ _) (y ~ _ ++ G0) _ G7); simpl_env; eauto.
      eclarify_ctx. solve_uniq. solve_uniq. simpl_env. solve_notin.
    + simpl. simpl_env.
      erewrite ctx_plus_app; eclarify_ctx; auto.
      erewrite ctx_plus_app; eclarify_ctx; auto.
      asimpl. 
      asimpl in x. erewrite ctx_plus_app in x; eclarify_ctx.
      eapply split_app in x; eclarify_ctx. destruct x.
      repeat f_equal. auto. auto.
Qed.



Lemma Typing_rename D2 G1 G2 x y B a q A : 
  Typing D2 G1 B a_Type ->
  Typing ((x ~ Tm B) ++ D2)  ((x ~ (q,Tm B)) ++ G2) a A ->
  y `notin` dom D2 ->
  Typing ((y ~ Tm B) ++ D2) ((y ~ (q,Tm B)) ++ G2) 
         (subst_tm_tm (a_Var_f y) x a) (subst_tm_tm (a_Var_f y) x A).
Proof.                 
  intros.
  move: (Typing_ctx H0) => C0. destruct_ctx.
  destruct (x == y).
  + subst. repeat rewrite subst_tm_id. auto.
  + have TV: Typing ((y ~ Tm B) ++ D2) ((y ~ (1, Tm B)) ++ ctx_mul 0 G1) (a_Var_f y) B.
    { eapply T_var; auto. }
    have WH: Typing ((x ~ Tm B) ++ (y ~ Tm B) ++ D2) (x ~ (q,Tm B) ++ (y ~ (0, Tm B)) ++ G2) a A. 
    { eapply weakening. auto. solve_ctx. eauto. }
    move: (fun x1 x2 => substitution x1 nil x2 nil) => s.
    eapply s in TV. 2: { simpl_env. eapply WH. }
    asimpl in TV.
    erewrite ctx_ctx_plus_0_r in TV.
    eapply TV. eclarify_ctx. eclarify_ctx.
Qed.


Lemma T_pi_exists :  forall x (D5 : D) (G1 G2 : context) 
         (q : usage) (A B : tm) (r : usage),
       Typing D5 G1 A a_Type ->
       Typing ([(x, Tm A)] ++ D5) ([(x, (r, Tm A))] ++ G2)
          (open_tm_wrt_tm B (a_Var_f x)) a_Type ->
       x `notin` dom D5 \u fv_tm_tm B ->
       Typing D5 (ctx_plus G1 G2) (a_Pi q A B) a_Type.
Proof.
  intros.
  eapply T_pi with (G1:=G1)(L := dom D5); eauto.
  intros y Fr.
  eapply Typing_rename with (y:=y) in H0; eauto.
  asimpl in H0.
  destruct (x == y). 
  + subst. erewrite subst_tm_id in H0. eauto.
  + erewrite subst_tm_tm_intro. eauto.
  fsetdec.
Qed.

Lemma T_Sigma_exists :  forall x (D5 : D) (G1 G2 : context) 
         (q : usage) (A B : tm) (r : usage),
       Typing D5 G1 A a_Type ->
       Typing ([(x, Tm A)] ++ D5) ([(x, (r, Tm A))] ++ G2)
          (open_tm_wrt_tm B (a_Var_f x)) a_Type ->
       x `notin` dom D5 \u fv_tm_tm B ->
       Typing D5 (ctx_plus G1 G2) (a_Sigma q A B) a_Type.
Proof.
  intros.
  eapply T_Sigma with (G1:=G1)(L := dom D5); eauto.
  intros y Fr.
  eapply Typing_rename with (y:=y) in H0; eauto.
  asimpl in H0.
  destruct (x == y). 
  + subst. erewrite subst_tm_id in H0. eauto.
  + erewrite subst_tm_tm_intro. eauto.
  fsetdec.
Qed.




Lemma invert_pi : forall D G q A B A0,
  Typing D G (a_Pi q A B) A0 ->
  Beta A0 a_Type /\
  exists G1, exists G2, exists r,
      ctx_sub D (ctx_plus G1 G2) G /\
      Typing D G1 A a_Type /\
      forall x, x `notin` dom D \u fv_tm_tm B ->
           Typing ([(x, Tm A)] ++ D) ([(x, (r, Tm A))] ++ G2)
                  (open_tm_wrt_tm B (a_Var_f x)) a_Type.
Proof.
intros.
dependent induction H.  
- (* sub *) 
  move: (IHTyping _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? ?]]]]]].
  split; auto.
  eexists. eexists. eexists.
  split; eauto.
  transitivity G1; auto.
- (* weak *) 
  move: (IHTyping1 _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  split; auto.
  clear IHTyping1 IHTyping2.
  exists (x ~ (0,Tm A0) ++ G1'). exists (x ~ (0,Tm A0) ++ G2'). eexists.
  repeat split.
  + asimpl.
    econstructor; eauto.
    reflexivity. 
  + eapply T_weak; eauto.
  + intros y Fr.
    asimpl in Fr.
    specialize (hb y ltac:(auto)). 
    eapply weakening. eapply hb. 
    move: (Typing_ctx hb) => CB.
    destruct_ctx.
    eclarify_ctx. 
    simpl_env. fsetdec.
    eauto.
- (* pi *) 
  split; auto.
  pick fresh z. move:(H0 z ltac:(auto)) => h.
  move: (Typing_ctx h) => C0. destruct_ctx.
  clear IHTyping H1. 
  exists G1. exists G2. exists r.
  repeat split.  
  + eapply ctx_sub_refl. eclarify_ctx.
  + auto.
  + intros.
  pick fresh y for (L \u {{x}} \u dom D5 \u fv_tm_tm B).
  specialize (H0 y ltac:(auto)).
  eapply Typing_rename with (y:= x) in H0; eauto.
  asimpl in H0.
  rewrite <- subst_tm_tm_intro in H0.
  auto.
  fsetdec.
- (* conv *) 
  move: (IHTyping1 _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  clear IHTyping1 IHTyping2.
  split.
  eapply B_Trans with (A1 := A0). eapply B_Sym. eauto. eauto.

  eexists. eexists. eexists.
  split.
  2: { split. eauto. 
       eauto. }
  transitivity G1. auto.
  eapply ctx_sub_refl. eclarify_ctx.
Qed.

Lemma invert_Sigma : forall D G q A B A0,
  Typing D G (a_Sigma q A B) A0 ->
  Beta A0 a_Type /\
  exists G1, exists G2, exists r,
      ctx_sub D (ctx_plus G1 G2) G /\
      Typing D G1 A a_Type /\
      forall x, x `notin` dom D \u fv_tm_tm B ->
           Typing ([(x, Tm A)] ++ D) ([(x, (r, Tm A))] ++ G2)
                  (open_tm_wrt_tm B (a_Var_f x)) a_Type.
Proof.
intros.
dependent induction H.  
- (* sub *) 
  move: (IHTyping _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? ?]]]]]].
  split; auto.
  eexists. eexists. eexists.
  split; eauto.
  transitivity G1; auto.
- (* weak *) 
  move: (IHTyping1 _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  split; auto.
  clear IHTyping1 IHTyping2.
  exists (x ~ (0,Tm A0) ++ G1'). exists (x ~ (0,Tm A0) ++ G2'). eexists.
  repeat split.
  + asimpl.
    econstructor; eauto.
    reflexivity. 
  + eapply T_weak; eauto.
  + intros y Fr.
    asimpl in Fr.
    specialize (hb y ltac:(auto)). 
    eapply weakening. eapply hb. 
    move: (Typing_ctx hb) => CB.
    destruct_ctx.
    eclarify_ctx. 
    simpl_env. fsetdec.
    eauto.
- (* conv *) 
  move: (IHTyping1 _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  clear IHTyping1 IHTyping2.
  split.
  eapply B_Trans with (A1 := A0). eapply B_Sym. eauto. eauto.

  eexists. eexists. eexists.
  split.
  2: { split. eauto. 
       eauto. }
  transitivity G1. auto.
  eapply ctx_sub_refl. eclarify_ctx.

- (* sigma *) 
  split; auto.
  pick fresh z. move:(H0 z ltac:(auto)) => h.
  move: (Typing_ctx h) => C0. destruct_ctx.
  clear IHTyping H1. 
  exists G1. exists G2. exists r.
  repeat split.  
  + eapply ctx_sub_refl. eclarify_ctx.
  + auto.
  + intros.
  pick fresh y for (L \u {{x}} \u dom D5 \u fv_tm_tm B).
  specialize (H0 y ltac:(auto)).
  eapply Typing_rename with (y:= x) in H0; eauto.
  asimpl in H0.
  rewrite <- subst_tm_tm_intro in H0.
  auto.
  fsetdec.
Qed.
