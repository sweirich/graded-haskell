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
Require Import structural.

Require Export beta.
  
(* Lemma 6.1 *)
Lemma Typing_regularity : 
  forall {D G a B}, Typing D G a B -> exists G', Typing D G' B a_Type.
Proof.
  intros. induction H.
  all: try destruct IHTyping as [G' h].
  all: try destruct IHTyping1 as [G1' h1].
  all: try destruct IHTyping2 as [G2' h2].

  all: try solve [eexists; eauto].
  all: try solve [eexists; eapply T_weak; eauto].
  - pick fresh x for (L \u fv_tm_tm B \u dom D5).
    specialize (H x ltac:(auto)).
    specialize (H0 x ltac:(auto)).
    destruct H0 as [G0 h0].
    move: (Typing_ctx h0) => C0.
    destruct_ctx.
    eexists.
    eapply (T_pi_exists x); eauto.
    asimpl in h0.
    eapply h0.
  - apply invert_pi in h1.
    move: h1 => [_ [G1'' [G2'' [r [? [? hb]]]]]].
    pick fresh x for (dom D5 \u fv_tm_tm B).
    specialize (hb x ltac:(auto)).  
    move: (substitution _ nil _ nil _ _ _ _ _ hb _ _ H0) => hs.
    asimpl in hs.
    erewrite <- subst_tm_tm_intro in hs; auto.
    eauto.
  - (* UnitE *) 
    pick_fresh x.
    specialize (H2 x ltac:(auto)).
    have LC: lc_tm a. { eapply Typing_lc; eauto. }
    move: (fun x y => substitution x nil y nil) => s.
    eapply s in H. 2: { simpl_env. apply H2. }
    simpl_env in H.
    rewrite subst_tm_tm_open_tm_wrt_tm in H; auto.
    rewrite subst_tm_same in H; auto.
    simpl in H.
    rewrite subst_tm_tm_fresh_eq in H. fsetdec.
    eexists. eauto.
  - (* unbox *)
    pick_fresh x.
    specialize (H2 x ltac:(auto)).
    have LC: lc_tm a. { eapply Typing_lc; eauto. }
    move: (fun x y => substitution x nil y nil) => s.
    eapply s in H. 2: { simpl_env. apply H2. }
    simpl_env in H.
    rewrite subst_tm_tm_open_tm_wrt_tm in H; auto.
    rewrite subst_tm_same in H; auto.
    simpl in H.
    rewrite subst_tm_tm_fresh_eq in H. fsetdec.
    eexists. eauto.
  - (* inj1 *)
    eexists. eapply T_sum; eauto.
  - (* inj2 *)
    eexists. eapply T_sum; eauto.
  - (* case *)
    pick fresh x.
    repeat match goal with [H : forall x, x `notin` ?L -> _ |- _ ] => specialize (H x ltac:(auto)) end.
    repeat match goal with [H : forall y, y `notin` ?L -> _ |- _ ] => specialize (H x ltac:(auto)) end.
    repeat match goal with [H : exists G' , Typing _ _ _ _ |- _ ] => destruct H end.
    move: (fun y => substitution D5 nil y nil) => s.
    match goal with [H5 : Typing _ _ (open_tm_wrt_tm ?B _) a_Type |- _ ] => 
                    eapply s in H5; eauto; clear s;
                    asimpl in H5;
                    rewrite subst_tm_tm_open_tm_wrt_tm in H5; eauto using Typing_lc;
                    rewrite subst_tm_same in H5; auto;
                    rewrite subst_tm_tm_fresh_eq in H5; eauto
    end.
  - pick fresh x for (L \u fv_tm_tm B \u dom D5).
    specialize (H1 x ltac:(auto)).
    specialize (H2 x ltac:(auto)).
    destruct H2 as [G0 h0].
    move: (Typing_ctx h0) => C0.
    destruct_ctx.
    eexists.
    eapply (T_Sigma_exists x); eauto.
  - (* spread *)
    subst A.
    pick fresh x.
    repeat match goal with [H : forall x, x `notin` ?L -> _ |- _ ] => specialize (H x ltac:(auto)) end.
    repeat match goal with [H : forall y, y `notin` ?L -> _ |- _ ] => specialize (H x ltac:(auto)) end.
    repeat match goal with [H : exists G' , Typing _ _ _ _ |- _ ] => destruct H end.
    move: (fun y => substitution D5 nil y nil) => s.
    match goal with [H5 : Typing _ _ (open_tm_wrt_tm ?B _) a_Type |- _ ] => 
                    eapply s in H5; eauto; clear s;
                    asimpl in H5;
                    rewrite subst_tm_tm_open_tm_wrt_tm in H5; eauto using Typing_lc;
                    rewrite subst_tm_same in H5; auto;
                    rewrite subst_tm_tm_fresh_eq in H5; eauto
    end.
Qed.

Lemma invert_Lam D G q a A C : 
  Typing D G (a_Lam q A a) C ->
     (forall x, x `notin` fv_tm_tm a `union` dom G `union` dom D -> 
           exists B,  Beta C (a_Pi q A B) /\
           exists G1, Typing D G1 (a_Pi q A B) a_Type /\
           Typing 
             (x ~ Tm A ++ D)
             ([(x, (q, Tm A))] ++ G) (open_tm_wrt_tm a (a_Var_f x)) 
                                     (open_tm_wrt_tm B (a_Var_f x))).      
Proof.      
  intros HA.
  dependent induction HA; intros y Fr.
  - have D: dom G1 = dom G2. eapply dom_ctx_sub; eauto.
    rewrite <- D in Fr.
    specialize (IHHA q a A ltac:(auto) y ltac:(auto)).
    move: IHHA => [B [HB [GA [hA HT]]]].
    exists B. split; auto. 
    exists GA. split; auto.
    eapply T_sub. eauto. econstructor; eauto. reflexivity. 
  - specialize (IHHA1 _ _ _  ltac:(auto) y ltac:(auto)).
    clear IHHA2.
    move: IHHA1 => [B0 [HB [GA [hA  HT]]]].
    exists B0. split. auto.
    exists (x ~ (0, Tm A0) ++ GA). split.
    eapply T_weak; eauto.
    eapply weakening. eauto. eclarify_ctx. solve_uniq. eauto.
  - (* lam *)
    clear IHHA. clear H0.
    exists B. split. 
    + eapply B_Refl. 
      pick fresh z. 
      move: (Typing_regularity (H z ltac:(auto))) => [GG TB].      
      eapply (lc_a_Pi_exists z);
      eapply Typing_lc; eauto.
    + pick fresh z.
      move: (H z ltac:(auto)) => h.
      move: (Typing_regularity h) => [G h1].
      move: (Typing_ctx h1) => C1.
      destruct_ctx.
      eexists. split.
      eapply (T_pi_exists z); eauto.
      eapply h1.
      move: (Typing_rename _ _ _ z y _ _ _ _ HA h ltac:(auto)) => rn.
      rewrite subst_tm_tm_open_tm_wrt_tm in rn. auto.
      rewrite subst_tm_same in rn. auto.
      rewrite subst_tm_tm_fresh_eq in rn. fsetdec.
      rewrite subst_tm_tm_open_tm_wrt_tm in rn. auto.
      rewrite subst_tm_same in rn. auto.
      rewrite subst_tm_tm_fresh_eq in rn. fsetdec.
      eapply rn.
  - (* conv *)
    specialize (IHHA1 _ _ _ ltac:(reflexivity) y Fr).
    destruct IHHA1 as [B0 [BB [G2' [T1 T2]]]]. clear IHHA2.
    exists B0.
    split. eapply B_Trans. eapply B_Sym. eauto. eauto.
    exists G2'. split. eauto.
    eauto.
Qed.



Lemma invert_Unit {D G A} :
  Typing D G a_TmUnit A -> 
  exists G1, Beta A a_TyUnit /\ ctx_mul 0 G1 = G1 /\ ctx_sub D G1 G.
Proof.
  intros HA.
  dependent induction HA.
  - destruct IHHA as [G3 [h0 [ h1 h2]]]; auto.
    exists G3. subst. repeat split; auto. transitivity G1; auto.
  - destruct IHHA1 as [G3 [h0 [h1 h2]]]; auto. clear IHHA2.
    exists (x ~ (0, Tm A) ++ G3). repeat split; auto. simpl.  ring_simpl. f_equal.  auto. 
    econstructor; auto. reflexivity.
  - destruct IHHA1 as [G3 [h0 [h1 h2]]]; auto.
    exists G3. repeat split; auto.
    eapply B_Trans. eapply B_Sym. eauto. eauto.
  - exists nil. repeat split; auto.
Qed.

Lemma invert_box {D G q a A} :
 Typing D G (a_box q a) A -> 
 exists A0,  
   Beta A (a_Box q A0) /\
   exists G0, ctx_sub D (ctx_mul q G0) G /\ Typing D G0 a A0.
Proof.
  intros HA.
  dependent induction HA.
  + edestruct IHHA as [A0 [HB [G0 [SS TA]]]]. eauto.
    eexists. split. eauto.
    exists G0. split.
    transitivity G1; auto. auto.
  + clear IHHA2.
    specialize (IHHA1 q a ltac:(auto)).
    move: IHHA1 => [A0 [HB [G0 [SS TA]]]].
    eexists. split. eauto.
    exists (x ~ (0, Tm A) ++ G0). split.
    econstructor. auto. rewrite qmul_0_r. reflexivity.
    eauto. eauto.
    eapply T_weak. eauto. auto. eauto.
  + clear IHHA2.
    specialize (IHHA1 q a ltac:(auto)).
    move: IHHA1 => [A0 [HB [G0 [SS TA]]]].
    eexists.  split. eapply B_Trans. eapply B_Sym; eauto. eauto.
    eexists. split. eauto. auto.
  + clear IHHA.
    move: (Typing_regularity HA) => [GA TA].
    eexists.  split. eapply B_Refl. econstructor. eapply Typing_lc; eauto.
    exists G. split.
    eapply ctx_sub_refl. eclarify_ctx.
    auto.
Qed.    

Lemma invert_Box {D G q A B} :
   Typing D G (a_Box q A) B -> 
   Beta B a_Type /\ Typing D G A a_Type.
Proof.
  intros HA. 
  dependent induction HA; intros.
  + specialize (IHHA _ _ ltac:(auto)). destruct IHHA.
    split. auto.
    eapply T_sub; eauto.
  + specialize (IHHA1 _ _ ltac:(auto)). destruct IHHA1.
    split. auto.
    eapply T_weak; eauto.
  + specialize (IHHA1 _ _ ltac:(auto)). destruct IHHA1.
    split. eapply B_Trans. eapply B_Sym. eauto. eauto. auto.
  + clear IHHA.
    split. eapply B_Refl. eauto. eauto.
Qed.

Lemma invert_inj1 : 
       forall {D G a A}, Typing D G (a_Inj1 a) A -> 
                    exists A1, exists A2, exists G1, Beta (a_Sum A1 A2) A /\
                                Typing D G a A1 /\ Typing D G1 A2 a_Type.
Proof. intros D G a A TA. dependent induction TA.
       - destruct (IHTA _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         exists A1. exists A2. eexists. split. auto. split.
         eapply T_sub; eauto. eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         eexists. eexists. eexists.
         split. eauto. split.
         eapply T_weak; auto. eauto.
         eapply T_weak; auto. eauto. eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         eexists. eexists. eexists.
         split. eapply B_Trans. eauto. eauto. 
         split; eauto.
       - eexists. eexists. eexists.
         split. eapply B_Refl. econstructor. eapply Typing_lc2; eauto. eapply Typing_lc; eauto.
         split; eauto.
Qed.


Lemma invert_inj2 : 
       forall {D G a A}, Typing D G (a_Inj2 a) A -> 
                    exists A1, exists A2, exists G1, Beta (a_Sum A1 A2) A /\
                                Typing D G a A2 /\ Typing D G1 A1 a_Type.
Proof. intros D G a A TA. dependent induction TA.
       - destruct (IHTA _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         exists A1. exists A2. eexists. split. auto. split.
         eapply T_sub; eauto. eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         eexists. eexists. eexists.
         split. eauto. split.
         eapply T_weak; auto. eauto.
         eapply T_weak; auto. eauto. eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         eexists. eexists. eexists.
         split. eapply B_Trans. eauto. eauto. 
         split; eauto.
       - eexists. eexists. eexists.
         split. eapply B_Refl. econstructor. eapply Typing_lc; eauto. eapply Typing_lc2; eauto.
         split; eauto.
Qed.

Lemma invert_Sum : forall {D G A1 A2 B},
       Typing D G (a_Sum A1 A2) B -> 
       Beta B a_Type /\ 
       exists G1, exists G2, ctx_sub D (ctx_plus G1 G2) G /\ Typing D G1 A1 a_Type /\ Typing D G2 A2 a_Type.
Proof.
       intros. dependent induction H.
       - destruct (IHTyping _ _ ltac:(auto)) as [Be [G1' [G2' [S [T1 T2]]]]]. 
         split. auto. exists G1'. exists G2'.
         split. transitivity G1; auto.
         split; auto.
       - destruct (IHTyping1 _ _ ltac:(auto)) as [Be [G1' [G2' [S [T1 T2]]]]]. 
         split. auto. exists (x ~ (0, Tm A) ++ G1'). exists (x ~ (0, Tm A) ++ G2').
         split. econstructor; eauto. ring_simpl; reflexivity.
         split. eapply T_weak; eauto.
                eapply T_weak; eauto.
       - destruct (IHTyping1 _ _ ltac:(auto)) as [Be [G1' [G2' [S [T1 T2]]]]]. 
         split. eapply B_Trans. eapply B_Sym. eauto. auto. 
         exists G1'. exists G2'. split. eauto. split. eauto. eauto.
       - split. eapply B_Refl. auto. 
         exists G1. exists G2. split. eapply ctx_sub_refl. eclarify_ctx.
         split; auto.
Qed.

Lemma invert_Tensor : forall {D G a1 a2 B},
       Typing D G (a_Tensor a1 a2) B -> 
       exists A1, exists A2, exists q, Beta B (a_Sigma q A1 A2) /\ 
       exists G1, exists G2, exists G3, exists r,
             ctx_sub D (ctx_plus (ctx_mul q G1) G2) G 
             /\ Typing D G1 a1 A1 
             /\ Typing D G2 a2 (open_tm_wrt_tm A2 a1)
             /\ (forall x, x `notin` dom D -> 
                    Typing (x ~ Tm A1 ++ D) (x ~ (r, Tm A1) ++ G3) (open_tm_wrt_tm A2 (a_Var_f x)) a_Type).
Proof.
  intros. dependent induction H.
  - destruct (IHTyping a1 a2 ltac:(auto)) as [A1 [A2 [q [BA [G1' [G2' [G3 [r [SS [Ta1 [Ta2 U]]]]]]]]]]].
    exists A1. exists A2. exists q. split. auto.
    exists G1'. exists G2'. exists G3. exists r.
    repeat split; auto. transitivity G1; auto.
  - destruct (IHTyping1 _ _ ltac:(auto))  as [A1 [A2 [q [BA [G1' [G2' [G3 [r [SS [Ta1 [Ta2 U]]]]]]]]]]].
    exists A1. exists A2. exists q. split. auto.
    exists (x ~ (0, Tm A) ++ G1'). exists (x ~ (0, Tm A) ++ G2'). exists (x ~ (0, Tm A) ++ G3). exists r.
    repeat split; auto. econstructor; eauto.  ring_simpl; reflexivity.
    eapply T_weak; eauto.
    eapply T_weak; eauto.
    intros. simpl in H2.
    move: (U x0 ltac:(auto)) => TB.
    eapply weakening; eauto.
    move: (Typing_ctx TB) => C. destruct_ctx.
    solve_ctx.
  - destruct (IHTyping1 _ _ ltac:(auto))  as [A1 [A2 [q [BA [G1' [G2' [G3 [r [SS [Ta1 [Ta2 U]]]]]]]]]]].
    exists A1. exists A2. exists q. split. eapply B_Trans. eapply B_Sym. eauto. auto.
    exists G1'. exists G2'. exists G3. exists r.
    repeat split; eauto.
  -  clear H2 IHTyping1 IHTyping2.
     move: (Typing_ctx H) => C1. move: (Typing_ctx H0) => C2.
     have LC: lc_tm (a_Sigma q A B). { 
       pick fresh z.
       eapply lc_a_Sigma_exists. eapply Typing_lc2; eauto.
       eapply Typing_lc; eauto.
     }
     exists A. exists B. exists q. split. apply B_Refl; auto.
     exists G1. exists G2. exists G3. exists r.
     repeat split; eauto.
     eapply ctx_sub_refl. solve_ctx.
     pick fresh z.
     intros x Frx.
     move: (Typing_regularity H) => [GA TA].
     move: (H1 z ltac:(auto)) => h.
     move: (Typing_regularity h) => [G h1].
     move: (Typing_ctx h1) => C3.
     destruct_ctx.
     move: (Typing_rename _ _ _ z x _ _ _ _ TA h ltac:(auto)) => rn.
     rewrite subst_tm_tm_open_tm_wrt_tm in rn. auto.
     rewrite subst_tm_same in rn. auto.
     rewrite subst_tm_tm_fresh_eq in rn. fsetdec.
     asimpl in rn.
     eapply rn.
Qed.


(* Theorem 6.4 *)
Lemma preservation: forall D G a A, Typing D G a A -> forall a', Step a a' -> Typing D G a' A.
Proof.
  induction 1; intros a' St.
  all: try solve [inversion St].
  - (* sub *) eapply T_sub; eauto.
  - (* weak *) eapply T_weak; eauto.
  - (* app *)
    inversion St; subst.
    + eapply T_app. eauto. auto.
    + (* beta *)
      clear IHTyping1. clear IHTyping2.
      move: (Typing_regularity  H) => [GP TP].
      move: (Typing_regularity  H0) => [GA TA].
      move: (invert_pi _ _ _ _ _ _ TP) => [M [G1' [G2' [r [S1 [T1 U]]]]]].

      pick fresh x for (fv_tm_tm a0 `union` dom D5 `union` fv_tm_tm B \u dom G1).
      move: (U x ltac:(auto)) => UU.

      rewrite (subst_tm_tm_intro x a0). fsetdec.
      rewrite (subst_tm_tm_intro x B). fsetdec.
      
      eapply invert_Lam with (x:=x) in H. 2: fsetdec.
      move: H => [B0 [EQ [GA0 [TP0 Ta]]]]. 
      move: (invert_Beta_a_Pi0 EQ) => h0.
      move: (invert_Beta_a_Pi1 EQ) => h1.
      move: (invert_Beta_a_Pi2 EQ) => h2.
      move: (invert_pi _ _ _ _ _ _ TP0) => [? [G3 [G4 [r1 [h3 [h4 h5]]]]]].
      subst q.
      move: (Typing_ctx_fv x TP0 ltac:(auto)) => FV. asimpl in FV.
      have h00: Typing D5 G2 b A0. eapply T_conv; eauto. 
      move: (substitution _ nil _ nil _ _ _ _ _ Ta _ _ h00) => SS.
      asimpl in SS.
      move: (Typing_regularity  SS) => [G0 TB0].
      move: (substitution _ nil _ nil _ _ _ _ _ UU _ _ H0) => SU. asimpl in SU.
      eapply T_conv. eauto. eauto.
      move: (h2 x ltac:(auto)) => BV.
      apply subst_Beta1. eapply Typing_lc; eauto.
      eapply B_Sym. auto.
 - (* beta *)
   eapply T_conv; eauto.
 - (* letunit *)
   inversion St; subst.
   + (* cong *)
     eapply T_conv.     
     eapply T_UnitE; eauto. 
     ++ pick fresh x.
       move: (H2 x ltac:(auto)) => h1.
       move: (substitution _ nil _ nil _ _ _ _ _ h1 _ _ H) => SU. asimpl in SU.
       rewrite subst_tm_tm_open_tm_wrt_tm in SU. eapply Typing_lc; eauto.
       rewrite subst_tm_tm_fresh_eq in SU. eauto.
       rewrite subst_tm_same in SU. auto. eauto.
     ++ pick fresh x. rewrite (subst_tm_tm_intro x). eauto. rewrite (subst_tm_tm_intro x B a). eauto.
        eapply subst_Beta2.
        move: (H3 x ltac:(auto)) => h. eapply Typing_lc. eauto.
        eapply B_Sym.
        eapply B_Step.
        auto.
   + (* beta *)
     move: (invert_Unit H) => [G4 [h0 [h1 h2]]].
     eapply T_sub. eauto.
     rewrite (ctx_plus_comm _ D5); eclarify_ctx.
     eapply ctx_plus_sub; eclarify_ctx.
     auto.
 - (* let box *)
   inversion St; subst.
   + (* Cong *)
     clear H1 H3.
     eapply T_conv.
     ++ eapply T_letbox with (L := L).
        eapply IHTyping. auto.
        move=> x Fr.
        eapply H0. auto.
        move=> x Fr.
        eapply H2. auto.
     ++ pick fresh x.
        move: (H2 x ltac:(auto)) => TB.
        move: (substitution _ nil _ nil _ _ _ _ _ TB _ _ H) => SU. asimpl in SU.
        rewrite subst_tm_tm_open_tm_wrt_tm in SU.
        eapply Typing_lc; eauto.
        rewrite subst_tm_same in SU. auto.
        rewrite subst_tm_tm_fresh_eq in SU. fsetdec.
        eauto.
     ++ pick fresh x. 
        move: (H2 x ltac:(auto)) => TB.
        rewrite (subst_tm_tm_intro x). eauto. 
        rewrite (subst_tm_tm_intro x B a). eauto.
        eapply subst_Beta2.
        eapply Typing_lc. eauto.
        eapply B_Sym.
        eapply B_Step.
        auto.
   + (* beta *)
     clear H3. clear H1.
     pick fresh x.
     move: (H0 x ltac:(auto)) => h1.
     move: (Typing_ctx h1) => CA. destruct_ctx.
     move: (invert_box H) => [A0 [BB [G [T1 T2]]]].
     move: (invert_Beta_Box1 BB) => BA.
     move: (invert_Beta_Box2 BB) => eq. subst q0.
     move: (Typing_regularity  H) => [GA TBA].
     move: (invert_Box TBA) => [h0 h2].
     have Ta0: (Typing D5 G a0 A). eapply T_conv. eapply T2. eauto. eapply B_Sym. eauto.
     move: (substitution _ nil _ nil _ _ _ _ _ h1 _ _ Ta0) => SU. asimpl in SU.
     rewrite subst_tm_tm_open_tm_wrt_tm in SU. eapply Typing_lc; eauto.
     rewrite subst_tm_same in SU. auto. 
     rewrite subst_tm_tm_open_tm_wrt_tm in SU. eapply Typing_lc; eauto.
     simpl in SU. rewrite eq_dec_refl in SU.
     rewrite subst_tm_tm_fresh_eq in SU. fsetdec.
     rewrite subst_tm_tm_fresh_eq in SU. fsetdec.
     eapply T_sub. eauto.
     erewrite ctx_plus_comm; eclarify_ctx.
     eapply ctx_sub_ctx_plus. auto.
     eapply ctx_sub_refl. auto.
 - (* case *)
   inversion St; subst.
   + (* case cong *)
     have TBa : Typing D5 (ctx_plus G3 (ctx_mul r G1)) (open_tm_wrt_tm B a) a_Type.
     {
       pick fresh x.
       match goal with [H5 : forall y, y `notin` L -> _ , 
                        H0  : Typing ?D ?G a _  |- _ ] =>
          move: (H5 x ltac:(auto)) => h1;
          move: (substitution _ nil _ nil _ _ _ _ _ h1 _ _ H0) => SU
       end.
       asimpl in SU.
       rewrite subst_tm_tm_open_tm_wrt_tm in SU.
       eapply Typing_lc; eauto.
       rewrite subst_tm_same in SU. auto.
       rewrite subst_tm_tm_fresh_eq in SU. fsetdec.
       eauto.
     }
     eapply T_conv.
     eapply T_case; auto.
     eauto.
     pick fresh x.
     rewrite (subst_tm_tm_intro x B a'0); auto.
     rewrite (subst_tm_tm_intro x B a); auto.
     eapply subst_Beta2.
     eapply Typing_lc. eauto. 
     eapply B_Sym.
     eapply B_Step.
     auto.
   + (* case Beta1 *)
     match goal with [H0 : Typing ?D ?G  _ (a_Sum _ _) |- _ ] =>
        move: (invert_inj1 H0) => [A1' [A2' [G1' [Be [T1 T2]]]]];
        move: (Typing_regularity H0) => [Gr TS]
     end.
     move: (invert_Beta_Sum1 Be) => Be1.
     move: (invert_Sum TS) => [BB [G3' [G4' [S [Ta Tb]]]]].
     eapply Typing_e.
     eapply T_app. eauto.
     eapply T_conv; eauto.  
     eapply ctx_plus_comm; eclarify_ctx.
     match goal with [H1 : forall x, x `notin` ?L -> (open_tm_wrt_tm B1 (a_Var_f x)) = _ |- _ ] => 
        pick fresh x;
        move: (H1 x ltac:(auto)) => E
     end.
     apply (cong (subst_tm_tm a0 x)) in E.
     rewrite subst_tm_tm_open_tm_wrt_tm in E; eauto using Typing_lc. 
     rewrite subst_tm_tm_open_tm_wrt_tm in E; eauto using Typing_lc. 
     simpl in E.  destruct (x == x) eqn:E1. rewrite E1 in E. 
     rewrite subst_tm_tm_fresh_eq in E; auto.
     rewrite subst_tm_tm_fresh_eq in E; auto.
     done.
   + (* case Beta1 *)
     match goal with [H0 : Typing ?D ?G  _ (a_Sum _ _) |- _ ] =>
        move: (invert_inj2 H0) => [A1' [A2' [G1' [Be [T1 T2]]]]];
        move: (Typing_regularity H0) => [Gr TS]
     end.
     move: (invert_Beta_Sum2 Be) => Be1.
     move: (invert_Sum TS) => [BB [G3' [G4' [S [Ta Tb]]]]].
     eapply Typing_e.
     eapply T_app. eauto.
     eapply T_conv; eauto.  
     eapply ctx_plus_comm; eclarify_ctx.
     match goal with [H1 : forall x, x `notin` ?L -> (open_tm_wrt_tm B2 (a_Var_f x)) = _ |- _ ] => 
        pick fresh x;
        move: (H1 x ltac:(auto)) => E
     end.
     apply (cong (subst_tm_tm a0 x)) in E.
     rewrite subst_tm_tm_open_tm_wrt_tm in E; eauto using Typing_lc. 
     rewrite subst_tm_tm_open_tm_wrt_tm in E; eauto using Typing_lc. 
     simpl in E.  destruct (x == x) eqn:E1. rewrite E1 in E. 
     rewrite subst_tm_tm_fresh_eq in E; auto.
     rewrite subst_tm_tm_fresh_eq in E; auto.
     done.
 - (* Spread *)
   inversion St; subst.
   + (* case cong *)
     have Ta0 : Typing D5 G1 a'0 (a_Sigma q A1 A2).
     { eapply IHTyping. eauto. }
     have TBa0 : Typing D5 (ctx_plus G3 (ctx_mul r G1)) (open_tm_wrt_tm B a'0) a_Type.
     {
       pick fresh x.
       match goal with [H5 : forall y, y `notin` L -> _ , 
                        H0  : Typing ?D ?G a'0 _  |- _ ] =>
          move: (H5 x ltac:(auto)) => h1;
          move: (substitution _ nil _ nil _ _ _ _ _ h1 _ _ H0) => SU
       end.
       asimpl in SU.
       rewrite subst_tm_tm_open_tm_wrt_tm in SU.
       eapply Typing_lc; eauto.
       rewrite subst_tm_same in SU. auto.
       rewrite subst_tm_tm_fresh_eq in SU. fsetdec.
       eauto.
     }

     have TBa : Typing D5 (ctx_plus G3 (ctx_mul r G1)) (open_tm_wrt_tm B a) a_Type.
     {
       pick fresh x.
       match goal with [H5 : forall y, y `notin` L -> _ , 
                        H0  : Typing ?D ?G a _  |- _ ] =>
          move: (H5 x ltac:(auto)) => h1;
          move: (substitution _ nil _ nil _ _ _ _ _ h1 _ _ H0) => SU
       end.
       asimpl in SU.
       rewrite subst_tm_tm_open_tm_wrt_tm in SU.
       eapply Typing_lc; eauto.
       rewrite subst_tm_same in SU. auto.
       rewrite subst_tm_tm_fresh_eq in SU. fsetdec.
       eauto.
     }

     eapply T_conv with (A := open_tm_wrt_tm B a'0).
     eapply T_Spread; auto.
     eauto.
     pick fresh x.
     rewrite (subst_tm_tm_intro x B a); auto.
     rewrite (subst_tm_tm_intro x B a'0); auto.
     eapply subst_Beta2.
     eapply Typing_lc. eauto. 
     eapply B_Sym.
     eapply B_Step.
     auto.
     
   + (* case beta *)
     move: (invert_Tensor H0) => [A1' [A2' [q1 [Be [G1' [G2' [G3' [r' ?]]]]]]]].
     move: (Typing_regularity H0) => [G' TS].
     move: (invert_Sigma _ _ _ _ _ _ TS) => [_ [G1'' [G2'' [r'' ?]]]].
     repeat match goal with [H : _ /\ _ |- _ ] => destruct H  end.
     move: (invert_Beta_a_Sigma1 Be) => Be1. 
     move: (invert_Beta_a_Sigma2 Be) => Be2. 
     move: (invert_Beta_a_Sigma0 Be) => Be3. 
     subst.

     pick fresh x. pick fresh y.
     specialize (H1 x ltac:(auto) y ltac:(auto)). move: H1 => Tb.
     move: (Typing_ctx Tb) => C1. 

     eapply substitution with (D2 := nil) (G2 := nil) (a := a0) in Tb.
     2: { eapply T_conv. eauto. eauto. eapply B_Sym. eauto. }
     asimpl in Tb.
     erewrite subst_tm_tm_open_tm_wrt_tm in Tb; eauto using Typing_lc.
     erewrite subst_tm_tm_close_tm_wrt_tm in Tb; eauto using Typing_lc.
     erewrite (subst_tm_tm_open_tm_wrt_tm B) in Tb; eauto using Typing_lc.
     simpl in Tb. destruct (x == x) eqn:E; rewrite E in Tb. 2: { done. } clear E e.
     destruct (y == x) eqn:E. { subst. clear Fr. solve_notin. }                                
     rewrite E in Tb. clear E n.
     rewrite subst_tm_tm_fresh_eq in Tb. { clear Fr0. fsetdec. }
     eapply Typing_e.
     eapply T_sub.
     3: { eauto. }
     eapply T_app.
     ++ eapply Tb.
     ++ eapply T_conv. eauto.
        replace a_Type with (subst_tm_tm a0 x a_Type).
        eapply substitution with (D2 := nil) (G2 := nil) (a := a0). simpl_env. 
        eapply H6. { clear Fr0. fsetdec. } eapply T_conv. eauto. eauto. eapply B_Sym. auto. reflexivity.
        rewrite (subst_tm_tm_intro x). { clear Fr0. fsetdec. }
        eapply subst_Beta1; eauto using Typing_lc.
     ++ destruct_ctx.
        simpl_env; eclarify_ctx.
        erewrite (ctx_plus_assoc _ _ G2); eclarify_ctx.
        erewrite ctx_plus_comm; eclarify_ctx.
        eapply ctx_sub_ctx_plus; eclarify_ctx. 
        eapply ctx_sub_refl; eclarify_ctx.
     ++ rewrite subst_tm_tm_fresh_eq. { clear Fr0. fsetdec. }
        rewrite <- subst_tm_tm_spec.
        rewrite subst_tm_tm_open_tm_wrt_tm. eauto using Typing_lc.
        rewrite subst_tm_tm_fresh_eq. { clear Fr. fsetdec. }
        f_equal.
        simpl.
        destruct (y == y) eqn:E. 2: { done. } rewrite E. 
        rewrite subst_tm_tm_fresh_eq. { clear Fr. fsetdec. }
        auto.
Qed.


Ltac invert_value :=
  match goal with [ H : value ?a|- _ ]=> inversion H end;
  try match goal with [ H : ty ?a |- _ ] => inversion H end.

Ltac inconsistent := 
  match goal with [ H : Beta ?a ?b |- _ ] => 
     apply Beta_consistent in H; eauto; inversion H
  end.

Lemma canonical_Type : forall a A, Typing nil nil a A -> Beta a a_Type -> value a -> ty a.
Proof.
  intros a A h.
  dependent induction h; intros; try solve [inconsistent]; try solve [invert_value]; eauto.
  - inversion H. subst. auto.
Qed.

Lemma canonical_Pi : forall a A q B1 B2, Typing nil nil a A -> Beta A (a_Pi q B1 B2) -> value a -> exists q1 a1 A1, a = a_Lam q1 A1 a1.
Proof. 
  intros. dependent induction H; intros; try solve [inconsistent]; try solve [invert_value]; eauto.
  - inversion H0; subst; eauto.
Qed.


Lemma canonical_Sigma : forall a A q B1 B2, Typing nil nil a A -> Beta A (a_Sigma q B1 B2) -> value a ->
                                       exists a1 b1, a = a_Tensor a1 b1.
Proof. 
  intros. dependent induction H; intros; try solve [inconsistent]; try solve [invert_value]; eauto.
  - inversion H0. subst. auto.
Qed.


Lemma canonical_Unit : forall a A, Typing nil nil a A -> Beta A a_TyUnit -> value a -> a = a_TmUnit.
Proof. 
  intros. dependent induction H; intros; try solve [inconsistent]; try solve [invert_value]; eauto.
  - inversion H0. subst. auto.
Qed.

Lemma canonical_Box : forall a A q B, Typing nil nil a A -> Beta A (a_Box q B) -> value a -> exists a1, a = a_box q a1.
Proof. 
  intros. dependent induction H; intros; try solve [inconsistent]; try solve [invert_value]; eauto.
  - inversion H0. subst. destruct IHTyping; auto. eauto.
  - move: (invert_Beta_Box2 H0) => h0. subst. eauto.
Qed.

Lemma canonical_Sum : forall a A B1 B2, Typing nil nil a A -> Beta A (a_Sum B1 B2) -> value a -> exists a1, a = a_Inj1 a1 \/ a = a_Inj2 a1.
Proof. 
  intros. dependent induction H; intros; try solve [inconsistent]; try solve [invert_value]; eauto.
  - inversion H0. subst. auto.
Qed.

(* Theorem 6.5 *)
Lemma progress : forall a A,
  Typing nil nil a A -> value a \/ exists a', Step a a'.
Proof. 
  intros a A H. dependent induction H; eauto.
  - inversion H0. subst. eauto.
  - move: (Typing_ctx H) => C. move: (Typing_ctx H0) => C0. destruct_ctx.
    destruct IHTyping1; auto.
    + (* fun is a value *)
      have LC: lc_tm a. eapply Typing_lc; eauto.
      eapply canonical_Pi in H; auto. 2: { eapply B_Refl; eauto using Typing_lc2.  }
      destruct H as [q1 [A1 [a1' E]]]; auto. subst.
      inversion LC. subst.
      right. eexists.
      eapply S_Beta; eauto using Typing_lc. 
    + (* fun steps *)
      destruct H1 as [a' SS].
      right. eexists. eauto using Typing_lc. 
  - move: (Typing_ctx H) => C. move: (Typing_ctx H1) => C0. destruct_ctx.
    destruct IHTyping1; auto.
    + eapply canonical_Unit in H; auto. subst.
      right. eexists.
      eapply S_UnitBeta; eauto using Typing_lc.
    + destruct H0 as [a' SS].
      right. eexists.
      eapply S_UnitCong; eauto using Typing_lc.
  - move: (Typing_ctx H) => C. destruct_ctx.
    destruct IHTyping; auto.
    + have LC: lc_tm a. eauto using Typing_lc.
      pick fresh y. 
      repeat match goal with [H : forall x, x `notin` ?L -> Typing _ _ _ _ |- _ ] => specialize (H y ltac:(auto)) end.
      move: (canonical_Box _ _ q A H) => h. 
      destruct h as [a1 E]; auto.
      eapply B_Refl; eauto using Typing_lc2. 
      subst.
      right. eexists.
      inversion LC.
      eapply S_BoxBeta; eauto using Typing_lc.
      eapply (lc_a_LetBoxB_exists y); eauto using Typing_lc.
      eapply (lc_a_Lam_exists y); eauto using Typing_lc, Typing_lc2.
      eapply (lc_a_Lam_exists y); eauto using Typing_lc2, Typing_lc2.
      eauto using Typing_lc.
    + destruct H4 as [a1 E]; auto.
      right. eexists.
      pick fresh y.
      eapply S_BoxCong; eauto using Typing_lc.
      eapply (lc_a_LetBoxB_exists y); eauto using Typing_lc.
      eapply (lc_a_Lam_exists y); eauto using Typing_lc, Typing_lc2.
      eapply (lc_a_Lam_exists y); eauto using Typing_lc2, Typing_lc2.
      eauto using Typing_lc.
  - move: (Typing_ctx H0) => C. destruct_ctx.
    have LC: lc_tm a. eapply Typing_lc; eauto.
    have LC2: lc_tm (a_Sum A1 A2). eapply Typing_lc2; eauto.
    destruct IHTyping1; auto.
    + eapply canonical_Sum in H0; auto. 
      destruct H0 as [a0 [V1 | V2]]; subst.
      ++ right.
         eexists.
         inversion LC.
         eapply S_Case1Beta; eauto using Typing_lc.
      ++ right. 
         eexists.
         inversion LC.
         eapply S_Case2Beta; eauto using Typing_lc.
    + destruct H7 as [a' SS].
      right. eexists.
      eapply S_CaseCong; eauto using Typing_lc.
  - right.
    move: (Typing_ctx H0) => C. destruct_ctx.
    have L1: lc_tm a by eauto using Typing_lc.
    have L2: lc_tm (a_Sigma q A1 A2) by eauto using Typing_lc2.
    have L4: lc_tm (a_Lam r (a_Sigma q A1 A2) B).
    { pick fresh y.
      move: (H3 y ltac:(auto)) => h.
      move: (Typing_lc h) => LB.
      eapply lc_a_Lam_exists. auto. eauto.
    }
    have L3: lc_tm (a_Spread a b (a_Lam r (a_Sigma q A1 A2) B)).
    { 
      pick fresh y. pick fresh z.
      move: (H1 y ltac:(auto) z ltac:(auto)) => Tb.
      move: (Typing_lc Tb) => LB.
      eapply lc_a_Spread_exists; eauto.
    }
    destruct IHTyping; eauto. 
    + have BB: Beta (a_Sigma q A1 A2) (a_Sigma q A1 A2).
      { eapply B_Refl; eauto. }
      move: (canonical_Sigma a _ q A1 A2 H0 BB H) => h.
      move: h => [a1 [b1 EQ]]. subst a.
      inversion L1. subst.
      eexists.
      eapply S_SpreadBeta; eauto using Typing_lc.
    + move: H => [a' SS].
      eexists. 
      eapply S_SpreadCong; eauto.
Qed.
