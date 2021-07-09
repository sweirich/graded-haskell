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
Require Import structural.

(* ------------------------------------------------------- *)

Lemma invert_Type {D G A} :
  Typing D G a_Type A -> 
  exists G1, Beta (subst_def D A) a_Type /\ ctx_mul 0 G1 = G1 /\ ctx_sub D G1 G.
Proof.
  intros HA.
  dependent induction HA.
  - destruct IHHA as [G3 [h0 [ h1 h2]]]; auto.
    exists G3. subst. repeat split; auto. transitivity G1; auto.
  - exists nil. repeat split; auto.

  - (* T_weak *) destruct IHHA1 as [G3 [h0 [h1 h2]]]; auto. clear IHHA2.
    exists (x ~ (0, Tm A) ++ G3). repeat split; auto. simpl.  ring_simpl. f_equal.  auto. 
    econstructor; auto. reflexivity.
  - (* T_weak_def *) destruct IHHA1 as [G3 [h0 [h1 h2]]]; auto. clear IHHA2.
    exists (x ~ (0, Def a A) ++ G3).
    repeat split. asimpl.
    erewrite subst_def_subst_tm_tm; eauto.
    replace a_Type with (subst_tm_tm (subst_def D5 a) x a_Type); try reflexivity.
    eapply subst_Beta1. eapply subst_def_lc_tm; eauto using Typing_lc_ctx, Typing_lc. auto.
    eauto using Typing_ctx_wff_regularity.
    asimpl. f_equal. auto.
    econstructor; auto. reflexivity.
  - destruct IHHA1 as [G3 [h0 [h1 h2]]]; auto.
    exists G3. repeat split; auto.
    asimpl.
    eapply B_Trans. eapply B_Sym. eauto. eauto.
Qed.


Lemma invert_Unit {D G A} :
  Typing D G a_TmUnit A -> 
  exists G1, Beta (subst_def D A) a_TyUnit /\ ctx_mul 0 G1 = G1 /\ ctx_sub D G1 G.
Proof.
  intros HA.
  dependent induction HA.
  - destruct IHHA as [G3 [h0 [ h1 h2]]]; auto.
    exists G3. subst. repeat split; auto. transitivity G1; auto.
  - (* T_weak *) destruct IHHA1 as [G3 [h0 [h1 h2]]]; auto. clear IHHA2.
    exists (x ~ (0, Tm A) ++ G3). repeat split; auto. simpl.  ring_simpl. f_equal.  auto. 
    econstructor; auto. reflexivity.
  - (* T_weak_def *) destruct IHHA1 as [G3 [h0 [h1 h2]]]; auto. clear IHHA2.
    exists (x ~ (0, Def a A) ++ G3).
    repeat split.
    asimpl. 
    erewrite subst_def_subst_tm_tm; eauto.
    replace a_TyUnit with (subst_tm_tm (subst_def D5 a) x a_TyUnit); try reflexivity.
    eapply subst_Beta1. eapply subst_def_lc_tm; eauto using Typing_lc_ctx, Typing_lc. auto.
    eauto using Typing_ctx_wff_regularity.
    asimpl. f_equal. auto.
    econstructor; auto. reflexivity.
  - destruct IHHA1 as [G3 [h0 [h1 h2]]]; auto.
    exists G3. repeat split; auto.
    asimpl.
    eapply B_Trans. eapply B_Sym. eauto. eauto.
  - exists nil. repeat split; auto.
Qed.

Lemma invert_box {D G q a A} :
 Typing D G (a_box q a) A -> 
 exists A0,  
   Beta (subst_def D A) (a_Box q (subst_def D A0)) /\
   exists G0, ctx_sub D (ctx_mul q G0) G /\ Typing D G0 a A0.
Proof.
  intros HA.
  dependent induction HA.
  + edestruct IHHA as [A0 [HB [G0 [SS TA]]]]. eauto.
    eexists. split. eauto.
    exists G0. split.
    transitivity G1; auto. auto.
  + (* T_weak *) clear IHHA2.
    specialize (IHHA1 q a ltac:(auto)).
    move: IHHA1 => [A0 [HB [G0 [SS TA]]]].
    exists A0. split. asimpl. auto.
    exists (x ~ (0, Tm A) ++ G0). split.
    econstructor. auto. rewrite qmul_0_r. reflexivity.
    eauto. eauto.
    eapply T_weak. eauto. auto. eauto.
  + (* T_weak_def *) clear IHHA2.
    specialize (IHHA1 q a ltac:(auto)).
    move: IHHA1 => [A0 [HB [G0 [SS TA]]]].
    exists A0. split. asimpl.
          erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.
          erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.
          replace (a_Box q (subst_tm_tm (subst_def D5 a0) x (subst_def D5 A0))) with  (subst_tm_tm (subst_def D5 a0) x (a_Box q (subst_def D5 A0))); try reflexivity.
      eapply subst_Beta1. eauto using subst_def_lc_tm, Typing_lc_ctx, Typing_lc. auto.
    exists (x ~ (0, Def a0 A) ++ G0). split.
    econstructor. auto. rewrite qmul_0_r. reflexivity.
    eauto. eauto.
    eapply T_weak_def. eauto. auto. eauto.
  + clear IHHA2.
    specialize (IHHA1 q a ltac:(auto)).
    move: IHHA1 => [A0 [HB [G0 [SS TA]]]].
    eexists.  split. eapply B_Trans. eapply B_Sym; eauto. eauto.
    eexists. split. eauto. auto.
  + clear IHHA.    
    eexists.  split. 
    rewrite <- subst_def_Box.
    eapply subst_def_Beta; eauto using Typing_lc_ctx.
    eapply B_Refl. econstructor. eapply Typing_lc2; eauto.
    exists G. split.
    eapply ctx_sub_refl. eclarify_ctx. eauto.
Qed.    

Lemma invert_Box {D G q A B} :
   Typing D G (a_Box q A) B -> 
   Beta (subst_def D B) a_Type /\ Typing D G A a_Type.
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
    split. asimpl.
    erewrite subst_def_subst_tm_tm; eauto.
    replace a_Type with (subst_tm_tm (subst_def D5 a) x a_Type); try reflexivity.
    eapply subst_Beta1. eapply subst_def_lc_tm; eauto using Typing_lc_ctx, Typing_lc. auto.
    eauto using Typing_ctx_wff_regularity.
    eapply T_weak_def; eauto.
  + specialize (IHHA1 _ _ ltac:(auto)). destruct IHHA1.
    split. eapply B_Trans. eapply B_Sym. eauto. eauto. auto.
  + clear IHHA.
    split. 
    rewrite subst_def_Type.
    eapply B_Refl. eauto. eauto.
Qed.


Lemma invert_Pi : forall D G q A B A0,
  Typing D G (a_Pi q A B) A0 ->
  Beta (subst_def D A0) a_Type /\
  exists G1, exists G2, exists r,
      ctx_sub D (ctx_plus G1 G2) G /\
      Typing D G1 A a_Type /\
      forall x, x `notin` dom D \u fv_tm_tm (subst_def D B) ->
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
- (* weak def *)
  move: (IHTyping1 _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  clear IHTyping1 IHTyping2.
  split. 
  (* Beta equal to Type *)
  asimpl. 
  erewrite subst_def_subst_tm_tm; eauto.
  replace a_Type with (subst_tm_tm (subst_def D5 a) x a_Type); try reflexivity.
  eapply subst_Beta1. eapply subst_def_lc_tm; eauto using Typing_lc_ctx, Typing_lc. auto.
  eauto using Typing_ctx_wff_regularity.

  exists (x ~ (0,Def a A0) ++ G1'). exists (x ~ (0,Def a A0) ++ G2'). eexists.
  repeat split.
  + asimpl.
    econstructor; eauto.
    reflexivity. 
  + eapply T_weak_def; eauto.
  + intros y Fr.
    asimpl in Fr.
    rewrite <- fv_subst_def_lower in Fr; eauto using Typing_ctx_wff_regularity.
    rewrite <- fv_tm_tm_subst_tm_tm_lower in Fr.
    specialize (hb y).
    rewrite -> fv_subst_def in hb; eauto using Typing_ctx_wff_regularity.
    specialize (hb ltac:(fsetdec)).
    eapply weakening_sort. eapply hb. 
    move: (Typing_ctx hb) => CB.
    destruct_ctx.
    eclarify_ctx. 
    simpl_env. fsetdec.
    econstructor; eauto. 
- (* pi *) 
  pick fresh z. move:(H0 z ltac:(auto)) => h.
  move: (Typing_ctx h) => C0. destruct_ctx.
  clear IHTyping H1. 
  rewrite subst_def_Type. 
  split; auto.
  exists G1. exists G2. exists r.
  repeat split.  
  + eapply ctx_sub_refl. eclarify_ctx.
  + auto.
  + intros.
  pick fresh y for (L \u {{x}} \u dom D5 \u fv_tm_tm (subst_def D5 B) \u fv_tm_tm B).
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
  eapply B_Trans with (A1 := subst_def D5 A0). eapply B_Sym. eauto. eauto.
  eexists. eexists. eexists.
  split.
  2: { split. eauto. 
       eauto. }
  transitivity G1. auto.
  eapply ctx_sub_refl. eclarify_ctx.
Qed.

Lemma invert_Sigma : forall D G q A B A0,
  Typing D G (a_Sigma q A B) A0 ->
  Beta (subst_def D A0) a_Type /\
  exists G1, exists G2, exists r,
      ctx_sub D (ctx_plus G1 G2) G /\
      Typing D G1 A a_Type /\
      forall x, x `notin` dom D \u fv_tm_tm (subst_def D B) ->
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
- (* weak_def *) 
  move: (IHTyping1 _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  clear IHTyping1 IHTyping2.
  split.
  (* Beta equal to Type *)
  asimpl. 
  erewrite subst_def_subst_tm_tm; eauto.
  replace a_Type with (subst_tm_tm (subst_def D5 a) x a_Type); try reflexivity.
  eapply subst_Beta1. eapply subst_def_lc_tm; eauto using Typing_lc_ctx, Typing_lc. auto.
  eauto using Typing_ctx_wff_regularity.

  exists (x ~ (0,Def a A0) ++ G1'). exists (x ~ (0,Def a A0) ++ G2'). eexists.
  repeat split.
  + asimpl.
    econstructor; eauto.
    reflexivity. 
  + eapply T_weak_def; eauto.
  + intros y Fr.
    asimpl in Fr.
    rewrite <- fv_subst_def_lower in Fr; eauto using Typing_ctx_wff_regularity.
    rewrite <- fv_tm_tm_subst_tm_tm_lower in Fr.
    specialize (hb y).
    rewrite -> fv_subst_def in hb; eauto using Typing_ctx_wff_regularity.
    specialize (hb ltac:(fsetdec)).
    eapply weakening_sort. eapply hb. 
    move: (Typing_ctx hb) => CB.
    destruct_ctx.
    eclarify_ctx. 
    simpl_env. fsetdec.
    econstructor; eauto. 
- (* conv *)
  move: (IHTyping1 _ _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  clear IHTyping1 IHTyping2.
(*   pick fresh z. move: (hb z ltac:(auto)) => Thb. move: (Typing_ctx Thb) => C. destruct_ctx. clear dependent z. *)
  split.
  eapply B_Trans with (subst_def D5 A0); auto. 
  eexists. eexists. eexists.
  repeat split; eauto. 
- (* sigma *) 
  pick fresh z. move:(H0 z ltac:(auto)) => h.
  move: (Typing_ctx h) => C0. destruct_ctx.
  clear IHTyping H1. 
  rewrite subst_def_Type.
  split; auto.
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


Lemma invert_With : forall D G A B A0,
  Typing D G (a_With A B) A0 ->
  Beta (subst_def D A0) a_Type /\
  exists G1, exists G2, exists r,
      ctx_sub D (ctx_plus G1 G2) G /\
      Typing D G1 A a_Type /\
      forall x, x `notin` dom D \u fv_tm_tm (subst_def D B) ->
           Typing ([(x, Tm A)] ++ D) ([(x, (r, Tm A))] ++ G2)
                  (open_tm_wrt_tm B (a_Var_f x)) a_Type.
Proof.
intros.
dependent induction H.  
- (* sub *) 
  move: (IHTyping _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? ?]]]]]].
  split; auto.
  eexists. eexists. eexists.
  split; eauto.
  transitivity G1; auto.
- (* weak *) 
  move: (IHTyping1 _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
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
- (* weak_def *) 
  move: (IHTyping1 _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  clear IHTyping1 IHTyping2.
  split.
  (* Beta equal to Type *)
  asimpl. 
  erewrite subst_def_subst_tm_tm; eauto.
  replace a_Type with (subst_tm_tm (subst_def D5 a) x a_Type); try reflexivity.
  eapply subst_Beta1. eapply subst_def_lc_tm; eauto using Typing_lc_ctx, Typing_lc. auto.
  eauto using Typing_ctx_wff_regularity.

  exists (x ~ (0,Def a A0) ++ G1'). exists (x ~ (0,Def a A0) ++ G2'). eexists.
  repeat split.
  + asimpl.
    econstructor; eauto.
    reflexivity. 
  + eapply T_weak_def; eauto.
  + intros y Fr.
    asimpl in Fr.
    rewrite <- fv_subst_def_lower in Fr; eauto using Typing_ctx_wff_regularity.
    rewrite <- fv_tm_tm_subst_tm_tm_lower in Fr.
    specialize (hb y).
    rewrite -> fv_subst_def in hb; eauto using Typing_ctx_wff_regularity.
    specialize (hb ltac:(fsetdec)).
    eapply weakening_sort. eapply hb. 
    move: (Typing_ctx hb) => CB.
    destruct_ctx.
    eclarify_ctx. 
    simpl_env. fsetdec.
    econstructor; eauto. 
- (* conv *)
  move: (IHTyping1 _ _ ltac:(reflexivity)) => [E [G1' [G2' [r [? [? hb]]]]]].
  clear IHTyping1 IHTyping2.
  split.
  eapply B_Trans with (subst_def D5 A0); auto. 
  eexists. eexists. eexists.
  repeat split; eauto. 
- (* with *) 
  pick fresh z. move:(H0 z ltac:(auto)) => h.
  move: (Typing_ctx h) => C0. destruct_ctx.
  clear IHTyping H1. 
  rewrite subst_def_Type.
  split; auto.
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
  - exists (x ~ (0, Def a A) ++ G').
    eapply weakening_sort with (D1 :=nil) (G1:=nil); eauto.
    econstructor; eauto. eapply Typing_ctx; eauto.
  - exists (x ~ (0, Def a A) ++ G1').
    eapply weakening_sort with (D1 :=nil) (G1:=nil); eauto.
    econstructor; eauto. eapply Typing_ctx; eauto.
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
  - apply invert_Pi in h1.
    move: h1 => [_ [G1'' [G2'' [r [? [? hb]]]]]].
    pick fresh x for (dom D5 \u fv_tm_tm (subst_def D5 B) \u fv_tm_tm B).
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
  - (* with *)
    pick fresh x.
    repeat match goal with [H : forall x, x `notin` ?L -> _ |- _ ] => specialize (H x ltac:(auto)) end.
    repeat match goal with [H : exists G' , Typing _ _ _ _ |- _ ] => destruct H end.
    eexists.
    eapply T_With_exists with (x:=x); eauto.
  - (* Prj1 *)
    move: (invert_With _ _ _ _ _ h) => [Be [G0 [G2 [Ta [r [Sub Tb]]]]]].
    eexists.
    eauto.
  - (* Prj2 *)
    move: (invert_With _ _ _ _ _ h) => [Be [G0 [G2 [Ta [r [Sub Tb]]]]]].
    pick fresh z for (dom D5 \u fv_tm_tm (subst_def D5 B) \u fv_tm_tm B). 
    specialize (Tb z ltac:(auto)).
    have Tp1: Typing D5 G (a_Prj1 a) A; eauto.
    eapply substitution with (D2 := nil) (G2 := nil)  in Tp1.
    2: { simpl_env. eapply Tb. }
    asimpl in Tp1.
    rewrite subst_tm_tm_open_tm_wrt_tm in Tp1; eauto using Typing_lc.
    rewrite subst_tm_same in Tp1; auto.
    rewrite subst_tm_tm_fresh_eq in Tp1; auto.
    eexists.
    eauto.
Qed.


Lemma invert_Lam D G q a A C : 
  Typing D G (a_Lam q A a) C ->
     (forall x, x `notin` fv_tm_tm a `union` dom G `union` dom D -> 
           exists B,  Beta (subst_def D C) (subst_def D (a_Pi q A B)) /\
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
  - (* T_weak *) 
    specialize (IHHA1 _ _ _  ltac:(auto) y ltac:(auto)).
    clear IHHA2.
    move: IHHA1 => [B0 [HB [GA [hA  HT]]]].
    exists B0. split. auto.
    exists (x ~ (0, Tm A0) ++ GA). split.
    eapply T_weak; eauto.
    eapply weakening. eauto. eclarify_ctx. solve_uniq. eauto.
  - (* T_weak_def *)
    specialize (IHHA1 _ _ _  ltac:(auto) y ltac:(auto)).
    clear IHHA2.
    move: IHHA1 => [B0 [HB [GA [hA  HT]]]].
    exists B0. split. simpl. 
    rewrite subst_def_Pi.
    repeat erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.
    eapply (subst_Beta1 (subst_def D5 a0) x) in HB; eauto using Typing_lc, subst_def_lc_tm, Typing_lc_ctx.
    rewrite subst_def_Pi in HB. simpl in HB. auto.

    exists (x ~ (0, Def a0 A0) ++ GA). split.
    eapply T_weak_def; eauto.
    eapply weakening_sort. eauto. eclarify_ctx. solve_uniq. eauto. 

  - (* lam *)
    clear IHHA. clear H0.
    exists B. split.
      eapply subst_def_Beta. eauto using Typing_lc_ctx.
      eapply B_Refl. 
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
      rewrite subst_tm_tm_fresh_eq in rn. {  clear Fr H3 H8. fsetdec. }
      rewrite subst_tm_tm_open_tm_wrt_tm in rn. auto.
      rewrite subst_tm_same in rn. auto.
      rewrite subst_tm_tm_fresh_eq in rn. { clear Fr H3 H8. fsetdec. }
      eapply rn.
  - (* conv *)
    specialize (IHHA1 _ _ _ ltac:(reflexivity) y Fr).
    destruct IHHA1 as [B0 [BB [G2' [T1 T2]]]]. clear IHHA2.
    exists B0.
    split. eapply B_Sym. eauto. eauto.
Qed.


Lemma invert_inj1 : 
       forall {D G a A}, Typing D G (a_Inj1 a) A -> 
                    exists A1, exists A2, exists G1, Beta (subst_def D (a_Sum A1 A2)) (subst_def D A) /\
                                Typing D G a A1 /\ Typing D G1 A2 a_Type.
Proof. intros D G a A TA. dependent induction TA.
       - destruct (IHTA _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         exists A1. exists A2. eexists. split. auto. split.
         eapply T_sub; eauto. eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         eexists. eexists. eexists.
         split. asimpl. eauto. split.
         eapply T_weak; auto. eauto.
         eapply T_weak; auto. eauto. eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         exists A1. exists A2. eexists.
         split. simpl.
         replace (a_Sum (subst_tm_tm a0 x A1) (subst_tm_tm a0 x A2)) with
                 (subst_tm_tm a0 x (a_Sum A1 A2)); try reflexivity.
         repeat erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.
         eapply subst_Beta1; eauto using Typing_lc, subst_def_lc_tm, Typing_lc_ctx.
         split.
         eapply T_weak_def; eauto.
         eapply T_weak_def; eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         eexists. eexists. eexists.
         split. eapply B_Trans. eauto. eauto. 
         split; eauto.
       - eexists. eexists. eexists.
         split.
         eapply subst_def_Beta. eauto using Typing_lc_ctx.
         eapply B_Refl. econstructor. eapply Typing_lc2; eauto. eapply Typing_lc; eauto.
         split; eauto.
Qed.


Lemma invert_inj2 : 
       forall {D G a A}, Typing D G (a_Inj2 a) A -> 
                    exists A1, exists A2, exists G1, Beta (subst_def D (a_Sum A1 A2)) (subst_def D A) /\
                                Typing D G a A2 /\ Typing D G1 A1 a_Type.
Proof. intros D G a A TA. dependent induction TA.
       - destruct (IHTA _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         exists A1. exists A2. eexists. split. auto. split.
         eapply T_sub; eauto. eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         eexists. eexists. eexists.
         split. asimpl. 
         eauto. split.
         eapply T_weak; auto. eauto.
         eapply T_weak; auto. eauto. eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         exists A1. exists A2. eexists.
         split. simpl.
         replace (a_Sum (subst_tm_tm a0 x A1) (subst_tm_tm a0 x A2)) with
                 (subst_tm_tm a0 x (a_Sum A1 A2)); try reflexivity.
         repeat erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.
         eapply subst_Beta1; eauto using Typing_lc, subst_def_lc_tm, Typing_lc_ctx.
         split.
         eapply T_weak_def; eauto.
         eapply T_weak_def; eauto.
       - destruct (IHTA1 _ ltac:(auto)) as [A1 [A2 [G1' [BA [T1 T2]]]]].
         eexists. eexists. eexists.
         split. eapply B_Trans. eauto. eauto. 
         split; eauto.
       - eexists. eexists. eexists.
         split. 
         eapply subst_def_Beta. eauto using Typing_lc_ctx.
         eapply B_Refl. econstructor. eapply Typing_lc; eauto. eapply Typing_lc2; eauto.
         split; eauto.
Qed.

Lemma invert_Sum : forall {D G A1 A2 B},
       Typing D G (a_Sum A1 A2) B -> 
       Beta (subst_def D B) a_Type /\ 
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
         split. asimpl. 

         (* Beta equal to Type *)
         asimpl. 
         erewrite subst_def_subst_tm_tm; eauto.
         replace a_Type with (subst_tm_tm (subst_def D5 a) x a_Type); try reflexivity.
         eapply subst_Beta1. eapply subst_def_lc_tm; eauto using Typing_lc_ctx, Typing_lc. auto.
         eauto using Typing_ctx_wff_regularity.

         exists (x ~ (0, Def a A) ++ G1'). exists (x ~ (0, Def a A) ++ G2').
         split. econstructor; eauto. ring_simpl; reflexivity.
         split. eapply T_weak_def; eauto.
                eapply T_weak_def; eauto.
       - destruct (IHTyping1 _ _ ltac:(auto)) as [Be [G1' [G2' [S [T1 T2]]]]]. 
         split. eapply B_Trans. eapply B_Sym. eauto. auto. 
         exists G1'. exists G2'. split. eauto. split. eauto. eauto.
       - split. 
         rewrite subst_def_Type.
         eapply B_Refl. auto. 
         exists G1. exists G2. split. eapply ctx_sub_refl. eclarify_ctx.
         split; auto.
Qed.



Lemma invert_Tensor : forall {D G a1 a2 B},
       Typing D G (a_Tensor a1 a2) B -> 
       exists A1, exists A2, exists q, Beta (subst_def D B) (subst_def D (a_Sigma q A1 A2)) /\ 
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
    exists A1. exists A2. exists q. split. asimpl.
    rewrite subst_def_Sigma.
    repeat erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.
    eapply (subst_Beta1 (subst_def D5 a) x) in BA; eauto using Typing_lc, subst_def_lc_tm, Typing_lc_ctx.
    rewrite subst_def_Sigma in BA. simpl in BA. auto.

    exists (x ~ (0, Def a A) ++ G1'). exists (x ~ (0, Def a A) ++ G2'). exists (x ~ (0, Def a A) ++ G3). exists r.
    repeat split; auto. asimpl. econstructor; eauto.  ring_simpl; reflexivity.
    eapply T_weak_def; eauto.
    eapply T_weak_def; eauto.
    intros. simpl in H2.
    move: (U x0 ltac:(auto)) => TB.
    eapply weakening_sort; eauto.
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
     exists A. exists B. exists q. split. eapply subst_def_Beta; eauto using Typing_lc_ctx. 
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
     rewrite subst_tm_tm_fresh_eq in rn. { clear Frx H5 H10. fsetdec. }
     asimpl in rn.
     eapply rn.
Qed.


Lemma invert_Pair : forall {D G a1 a2 B},
       Typing D G (a_Pair a1 a2) B -> 
       exists A1, exists A2, Beta (subst_def D B) (subst_def D (a_With A1 A2)) /\ 
       exists G3, exists r,
               Typing D G a1 A1 
             /\ Typing D G a2 (open_tm_wrt_tm A2 a1)
             /\ (forall x, x `notin` dom D -> 
                    Typing (x ~ Tm A1 ++ D) (x ~ (r, Tm A1) ++ G3) 
                           (open_tm_wrt_tm A2 (a_Var_f x)) a_Type).
Proof.
  intros. dependent induction H.
  - (* sub *) destruct (IHTyping a1 a2 ltac:(auto)) as [A1 [A2 [BA [G3 [r [Ta1 [Ta2 U]]]]]]].
    exists A1. exists A2. split. auto.
    exists G3. exists r.
    repeat split; auto.
    eapply T_sub; eauto.
    eapply T_sub; eauto.
  - (* weak *) destruct (IHTyping1 a1 a2 ltac:(auto)) as [A1 [A2 [BA [G3 [r [Ta1 [Ta2 U]]]]]]].
    clear IHTyping2.
    exists A1. exists A2. split. auto.
    exists (x ~ (0, Tm A) ++ G3). exists r.
    repeat split; auto.
    eapply T_weak; eauto.
    eapply T_weak; eauto.
    intros. simpl in H2.
    move: (U x0 ltac:(auto)) => TB.
    eapply weakening; eauto.
    move: (Typing_ctx TB) => C. destruct_ctx.
    solve_ctx.
  - (* weak_def *)
    destruct (IHTyping1 a1 a2 ltac:(auto)) as [A1 [A2 [BA [G3 [r [Ta1 [Ta2 U]]]]]]].
    clear IHTyping2.
    exists A1. exists A2. split. asimpl.
    rewrite subst_def_With.
    repeat erewrite subst_def_subst_tm_tm; eauto using Typing_ctx_wff_regularity.
    eapply (subst_Beta1 (subst_def D5 a) x) in BA; eauto using Typing_lc, subst_def_lc_tm, Typing_lc_ctx.
    rewrite subst_def_With in BA. simpl in BA. auto.
    exists (x ~ (0, Def a A) ++ G3). exists r.
    repeat split; auto.
    eapply T_weak_def; eauto.
    eapply T_weak_def; eauto.
    intros. simpl in H2.
    move: (U x0 ltac:(auto)) => TB.
    eapply weakening_sort; eauto.
    move: (Typing_ctx TB) => C. destruct_ctx.
    solve_ctx. 
  - destruct (IHTyping1 a1 a2 ltac:(auto)) as [A1 [A2 [BA [G3 [r [Ta1 [Ta2 U]]]]]]].
    clear IHTyping2.
    exists A1. exists A2. split. eapply B_Trans. eapply B_Sym. eauto. auto.
    exists G3. exists r.
    repeat split; eauto.    
  - clear H2 IHTyping1 IHTyping2.
     move: (Typing_ctx H) => C1. move: (Typing_ctx H0) => C2.
     have LC: lc_tm (a_With A B). { 
       pick fresh z.
       eapply lc_a_With_exists. eapply Typing_lc2; eauto.
       eapply Typing_lc; eauto.
     }
     exists A. exists B. split. eapply subst_def_Beta; eauto using Typing_lc_ctx. 
     exists G2. exists r.
     repeat split; eauto.
     pick fresh z.
     intros x Frx.
     move: (Typing_regularity H) => [GA TA].
     move: (H1 z ltac:(auto)) => h.
     move: (Typing_ctx h) => C3.
     destruct_ctx.
     move: (Typing_rename _ _ _ z x _ _ _ _ TA h ltac:(auto)) => rn.
     rewrite subst_tm_tm_open_tm_wrt_tm in rn. auto.
     rewrite subst_tm_same in rn. auto.
     rewrite subst_tm_tm_fresh_eq in rn. { fsetdec. }
     asimpl in rn.
     eapply rn.
Qed.
