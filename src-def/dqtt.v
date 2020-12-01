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
Require Export inversion.
  
(* Theorem 6.4 *)
Lemma preservation: forall D G a A, Typing D G a A -> forall a', Step a a' -> Typing D G a' A.
Proof.
  induction 1; intros a' St.
  all: try solve [inversion St].
  - (* sub *) eapply T_sub; eauto.
  - (* weak *) eapply T_weak; eauto.
  - (* weak_def *) eapply T_weak_def; eauto.
  - (* app *)
    inversion St; subst.
    + eapply T_app. eauto. auto.
    + (* beta *)
      clear IHTyping1. clear IHTyping2.
      move: (Typing_regularity  H) => [GP TP].
      move: (Typing_regularity  H0) => [GA TA].
      move: (invert_Pi _ _ _ _ _ _ TP) => [M [G1' [G2' [r [S1 [T1 U]]]]]].

      pick fresh x for (fv_tm_tm a0 `union` dom D5 `union` fv_tm_tm (subst_def D5 B) \u fv_tm_tm B \u dom G1).
      move: (U x ltac:(auto)) => UU.

      rewrite (subst_tm_tm_intro x a0). fsetdec.
      rewrite (subst_tm_tm_intro x B). fsetdec.
      
      eapply invert_Lam with (x:=x) in H. 2: fsetdec.
      move: H => [B0 [EQ [GA0 [TP0 Ta]]]]. 
      repeat rewrite subst_def_Pi in EQ; eauto using Typing_lc_ctx.
      move: (invert_Beta_a_Pi0 EQ) => h0.
      move: (invert_Beta_a_Pi1 EQ) => h1.
      move: (invert_Beta_a_Pi2 EQ) => h2.
      move: (invert_Pi _ _ _ _ _ _ TP0) => [? [G3 [G4 [r1 [h3 [h4 h5]]]]]].
      subst q.
      move: (Typing_ctx_fv x TP0 ltac:(auto)) => FV. asimpl in FV.
      have h00: Typing D5 G2 b A0. eapply T_conv; eauto. 
      move: (substitution _ nil _ nil _ _ _ _ _ Ta _ _ h00) => SS.
      asimpl in SS.
      move: (Typing_regularity  SS) => [G0 TB0].
      move: (substitution _ nil _ nil _ _ _ _ _ UU _ _ H0) => SU. asimpl in SU.
      eapply T_conv. eauto. eauto.
      have Frx: x `notin` fv_tm_tm (subst_def D5 B0). rewrite fv_subst_def. fsetdec. eauto using Typing_ctx_wff_regularity. 
      move: (h2 x ltac:(auto)) => BV.
      repeat erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.
      have LC: lc_tm (subst_def D5 b). eapply subst_def_lc_tm; eauto using Typing_lc_ctx.
      eapply subst_Beta1; auto.
      repeat rewrite subst_def_open_tm_wrt_tm; eauto using Typing_lc_ctx. 
      rewrite (subst_def_fresh_eq D5 (a_Var_f x)). intros x0 Fr0. simpl. fsetdec.
      auto.
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
        eapply subst_def_Beta; eauto using Typing_lc_ctx.
        eapply subst_Beta2.
        move: (H3 x ltac:(auto)) => h. eapply Typing_lc. eauto.
        eapply B_Sym; eauto.        
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
        eapply subst_def_Beta; eauto using Typing_lc_ctx.
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
     rewrite subst_def_Box in BB.
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
     rewrite subst_tm_tm_fresh_eq in SU. { clear H11. fsetdec. }
     rewrite subst_tm_tm_fresh_eq in SU. { clear H11. fsetdec. }
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
     eapply subst_def_Beta; eauto using Typing_lc_ctx.     
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
     repeat rewrite subst_def_Sum in Be.
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
     repeat rewrite subst_def_Sum in Be.
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
     eapply subst_def_Beta; eauto using Typing_lc_ctx.
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
     repeat rewrite subst_def_Sigma in Be.
     move: (invert_Beta_a_Sigma1 Be) => Be1. 
     move: (invert_Beta_a_Sigma2 Be) => Be2. 
     move: (invert_Beta_a_Sigma0 Be) => Be3. 
     subst.

     pick fresh x for (dom D5 \u fv_tm_tm (subst_def D5 A2) \u fv_tm_tm (subst_def D5 A2') \u L \u fv_tm_tm b \u fv_tm_tm A2' \u fv_tm_tm B). 
     pick fresh y.
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
        repeat erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.                                       
        eapply subst_Beta1; eauto using Typing_lc. eapply subst_def_lc_tm; eauto using Typing_lc_ctx. (* lc_tm (subst_def D5 a0) *)
        repeat erewrite subst_def_open_tm_wrt_tm.
        repeat erewrite (subst_def_fresh_eq D5 (a_Var_f x)).
        eapply B_Sym.
        eapply Be2.
        { clear Fr0. auto.  }
        { clear Fr0. intros. simpl. fsetdec. }
        all: eauto using Typing_lc_ctx.
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
 - (* Case Prj1 *)
   inversion St; subst.
   + move: (Typing_regularity H) => [G4 Tw].
     move: (invert_With _ _ _ _ _ Tw) => [Be0 [G1' [G2' [r [SS [TA h0]]]]]].
     move: (invert_Pair H) => [A' [B' [Be [G3 [r1 [h1 [h2 h3]]]]]]].
     eapply T_conv; eauto 1.
     repeat rewrite subst_def_With in Be.
     eapply B_Sym.
     eapply invert_Beta_a_With1. eauto.
   + eauto.
 - (* Case Prj2 *)
   inversion St; subst.
   + move: (Typing_regularity H) => [G4 Tw].
     move: (invert_With _ _ _ _ _ Tw) => [Be0 [G1' [G2' [r [SS [TA h0]]]]]].
     move: (invert_Pair H) => [A' [B' [Be [G3 [r1 [h1 [h2 h3]]]]]]].
     have Tpp: (Typing D5 G (a_Prj1 (a_Pair a0 a')) A). { eauto. }
     have Tpp': (Typing D5 G (a_Prj1 (a_Pair a0 a')) A'). { eauto. }
     eapply B_Sym in Be.
     repeat rewrite subst_def_With in Be.
     pick fresh x for (fv_tm_tm (subst_def D5 B') \u fv_tm_tm (subst_def D5 B) 
                                \u dom D5 \u fv_tm_tm B' \u fv_tm_tm B).
     eapply invert_Beta_a_With2 with (x0:=x) in Be; auto.
     specialize (h0 x ltac:(auto)).
     specialize (h3 x ltac:(auto)).
     eapply substitution with (D2:=nil) (G2:=nil) in Tpp. 2 : { simpl_env; eapply h0. }
     asimpl in Tpp.
     rewrite subst_tm_tm_open_tm_wrt_tm in Tpp; eauto using Typing_lc.
     rewrite subst_tm_same in Tpp; auto.
     rewrite subst_tm_tm_fresh_eq in Tpp; auto.

     eapply T_conv; eauto 1.

     eapply subst_Beta with (x:=x) (a0:=subst_def D5 a0)(a1:=subst_def D5 (a_Prj1 (a_Pair a0 a'))) in Be.     
     erewrite subst_tm_tm_open_tm_wrt_tm in Be; eauto using Typing_lc, Typing_lc_ctx, subst_def_lc_tm.
     rewrite subst_tm_same in Be; auto.
     rewrite subst_tm_tm_fresh_eq in Be; auto.
     
     erewrite subst_tm_tm_open_tm_wrt_tm in Be; eauto using Typing_lc, Typing_lc_ctx, subst_def_lc_tm.
     rewrite subst_tm_same in Be; auto.
     rewrite subst_tm_tm_fresh_eq in Be; auto.
     
     rewrite subst_def_open_tm_wrt_tm; eauto using Typing_lc_ctx.
     rewrite subst_def_open_tm_wrt_tm; eauto using Typing_lc_ctx.

     eapply subst_def_Beta; eauto using Typing_lc_ctx.

   + move: (Typing_regularity H) => [Gw Tw]. 
     move: (invert_With _ _ _ _ _ Tw) => [Be [G0 [G1 [r [SS [h0 h1]]]]]].
     eapply T_conv.
     eauto.
     pick fresh x for (dom D5 \u fv_tm_tm (subst_def D5 B) \u fv_tm_tm B). 
     have Tp1: Typing D5 G (a_Prj1 a) A. eauto.
     specialize (h1 x ltac:(auto)).
     eapply substitution with (D2 :=nil) (G2:=nil) in Tp1.
     2: { asimpl. eapply h1. }
     asimpl in Tp1.
     rewrite subst_tm_tm_open_tm_wrt_tm in Tp1. eauto using Typing_lc.
     rewrite subst_tm_same in Tp1; auto.
     rewrite subst_tm_tm_fresh_eq in Tp1; auto.
     eauto.
     pick fresh x for (dom D5 \u fv_tm_tm (subst_def D5 B) \u fv_tm_tm B \u fv_tm_tm a \u fv_tm_tm a'0). 
     specialize (h1 x ltac:(auto)).
     rewrite (subst_tm_tm_intro x B); auto.
     rewrite (subst_tm_tm_intro x B (a_Prj1 a)); auto.
     eapply subst_def_Beta. eapply Typing_lc_ctx; eauto.
     eapply subst_Beta2; eauto. eapply Typing_lc; eauto.    
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

Lemma canonical_Pair : forall a A B1 B2, Typing nil nil a A -> Beta A (a_With B1 B2) -> value a ->
                                       exists a1 b1, a = a_Pair a1 b1.
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
  - 
    move: (Typing_regularity H) => [Gr Hr].
    destruct IHTyping; eauto.    
    have BB: Beta (a_With A B) (a_With A B). eapply B_Refl; eauto using Typing_lc.
    + move: (canonical_Pair _ _ _ _ H BB H0) => [a1' [b1' h]]. subst.
      have LC: (lc_tm (a_Pair a1' b1')). eauto using Typing_lc. inversion LC.
      right.
      exists a1'. eapply S_Prj1Beta; eauto using Typing_lc.
    + move: H0 => [a' SS].
      right. exists (a_Prj1 a'). eapply S_Prj1Cong. auto.
   - move: (Typing_regularity H) => [Gr Hr].
    destruct IHTyping; eauto.    
    have BB: Beta (a_With A B) (a_With A B). eapply B_Refl; eauto using Typing_lc.
    + move: (canonical_Pair _ _ _ _ H BB H0) => [a1' [b1' h]]. subst.
      have LC: (lc_tm (a_Pair a1' b1')). eauto using Typing_lc. inversion LC.
      right.
      exists b1'. eapply S_Prj2Beta; eauto using Typing_lc.
    + move: H0 => [a' SS].
      right. exists (a_Prj2 a'). eapply S_Prj2Cong. auto.
Qed.
