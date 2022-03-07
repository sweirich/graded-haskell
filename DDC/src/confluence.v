Require Import Lia.
Require Import Coq.Program.Equality.
Require Export Qual.geq.
Require Export Qual.defeq.
Require Export Qual.par.

(* ------------------------------------------------------------------------ *)


Set Implicit Arguments.

Lemma Par_Abs_inv : forall {S D rho A1 a1 B}, Par S D (a_Abs rho A1 a1) B -> 
      exists B1 b1, 
          B = (a_Abs rho B1 b1) 
        /\ forall x, x `notin` fv_tm_tm a1 \u fv_tm_tm b1 \u dom S ->
               Par ([(x,rho)]++S) D (open a1 (a_Var_f x)) (open b1 (a_Var_f x))
        /\ CPar S D q_Top A1 B1.
Proof. 
  intros S D rho A1 a1 B h. 
  dependent induction h.
  all: try invert_Grade; subst. 
  all: eexists; eexists.
  all: split; try reflexivity; intros; split.
  all: pick fresh y.
  + eapply Par_Refl; eauto.
    eapply (@Grade_renaming y); eauto. 
  + invert_CGrade A1; eauto.
  + repeat spec y.
    eapply (@Par_renaming y); eauto.
  + auto.
Qed.

Lemma Par_WPair_inv : forall {S D rho a0 a1 B}, Par S D (a_WPair a0 rho a1) B -> 
      exists b0 b1, 
          B = (a_WPair b0 rho b1) 
        /\ (CPar S D rho a0 b0) 
        /\ Par S D a1 b1.
Proof. 
  intros S D rho a0 a1 B h. dependent induction h.
  all: try invert_Grade; subst;
        eexists; eexists; split; try reflexivity; split.
  all: repeat split.
  all: intros; try done.
  all: try eapply Par_Refl; eauto.
  invert_CGrade a0; auto.
Qed.

Lemma Par_SPair_inv : forall {S D rho a0 a1 B}, Par S D (a_SPair a0 rho a1) B -> 
      exists b0 b1, 
          B = (a_SPair b0 rho b1) 
        /\ (CPar S D rho a0 b0) 
        /\ Par S D a1 b1.
Proof. 
  intros S D rho a0 a1 B h. dependent induction h.
  all: try invert_Grade; subst;
        eexists; eexists; split; try reflexivity; split.
  all: intros; try done.
  all: try eapply Par_Refl; eauto.
  invert_CGrade a0; auto.
Qed.


Lemma Par_Inj1_inv : forall {S D a0 B}, Par S D (a_Inj1 a0) B -> 
      exists b0, 
          B = (a_Inj1 b0) 
        /\ Par S D a0 b0.
Proof. 
  intros S D a0 B h. dependent induction h.
  all: try invert_Grade; subst;
        eexists; split; try reflexivity.
  all: intros; try done.
  all: try eapply Par_Refl; eauto.
Qed.

Lemma Par_Inj2_inv : forall {S D a0 B}, Par S D (a_Inj2 a0) B -> 
      exists b0, 
          B = (a_Inj2 b0) 
        /\ Par S D a0 b0.
Proof. 
  intros S D a0 B h. dependent induction h.
  all: try invert_Grade; subst;
        eexists; split; try reflexivity.
  all: intros; try done.
  all: try eapply Par_Refl; eauto.
Qed.


(* ----------------------------------------------------------------------------------- *)

Local Ltac use_size_induction a ac Par1 Par2 :=
  lazymatch goal with
  | [   IH : forall y: nat, ?T,
        H : Par ?G ?psi a ?b0,
        H4 : Par ?G ?psi a ?b1 |- _ ] =>
      move: (@IH (size a) ltac:(lia) a ltac:(auto) _ _ _ H _ H4) => [ ac [Par1 Par2]]
  end.
Local Ltac use_size_induction_open a0 x ac Par1 Par2 :=
   let h0 := fresh in
   let h1 := fresh in
   let EQ1 := fresh in
   lazymatch goal with
        | [  H : forall x : atom,
              x `notin` ?L
              -> Par ?S ?psi (?open a0 (?a_Var_f x)) ?b
          ,  H4: forall x : atom,
              x `notin` ?L0
              -> Par ?S ?psi (?open a0 (?a_Var_f x)) ?c
          |- _ ] =>
    move: (@H x ltac:(auto)) => h0; clear H;
    move: (@H4 x ltac:(auto)) => h1; clear H4;
    pose proof (EQ1 := size_open_var a0 x);
    use_size_induction (open a0 (a_Var_f x)) ac Par1 Par2;
    clear h0; clear h1; clear EQ1
  end.

Local Ltac invert_equality :=
  match goal with
  | [ H : _ = _ |- _ ] => inversion H ; clear H
  end.

Lemma confluence_size : 
  forall n (a:tm), (size a <= n)%nat -> forall S psi a1, 
      Par S psi a a1 -> forall a2, Par S psi a a2 -> exists b, Par S psi a1 b /\ Par S psi a2 b.
Proof.
  pose confluence_size_def n :=
      forall (a:tm), (size a <= n)%nat ->  forall S psi a1, Par S psi a a1 -> forall a2, Par S psi a a2 -> exists b, Par S psi a1 b /\ Par S psi a2 b.
  intro n. fold (confluence_size_def ltac:(typeclasses eauto) n).  eapply (well_founded_induction_type lt_wf).
  clear n. intros n IH. unfold confluence_size_def in *. clear confluence_size_def.
  intros a SZ S psi a1 P1 a2 P2.
  inversion P1; inversion P2; subst.
  (* 441 subgoals *)
  all: try solve [invert_equality].

  (* 75 subgoals *)
  (* refl left *)
  all: try solve [
  match goal with
      | [ P2 : Par _ _ ?b ?b |- exists cc:tm, Par ?S ?D ?b cc /\ Par ?S ?D ?a2 cc ] =>
        exists a2 
      end; split; eauto using Par_Grade2].
  (*  54 subgoals *)
  all: try solve [
  match goal with
      | [ P2 : Par _ _ ?b ?b |- exists cc:tm, Par ?S ?D ?a2 cc /\ Par ?S ?D ?b cc ] =>
        exists a2
      end;  split; eauto using Par_Grade2].
  (* 34 subgoals *)
  all: try invert_equality; subst. 
  all: simp_syntax_in SZ; destruct n.
  all: try solve [ inversion SZ ].
  all: try done.
  - (* pi cong / pi cong *)
    use_size_induction A1 ac Par1 Par2.
    pick fresh x.
    use_size_induction_open B1 x bc Par3 Par4.
    exists (a_Pi psi1 ac (close x bc));
    split; eauto;
    exists_apply_Par x; eauto.
  - (* two betas *)
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    subst;
    try done.
    (* both rel *)
    + use_size_induction b bc Par1 Par2.
      use_size_induction a0 a0c Par3 Par4.
      move: (Par_Abs_inv Par3) => [A'1 [a1' ?]].
      move: (Par_Abs_inv Par4) => [A'2 [a'2 ?]].
      split_hyp; subst; invert_equality; subst.
      exists (open a'2 bc).
      pick fresh x. repeat spec x. split_hyp.
      split.
      eapply open2; eauto.
      eapply open2; eauto.
    + (* both irrel *)
      use_size_induction a0 a0c Par3 Par4.
      move: (Par_Abs_inv Par3) => [A'1 [a1' ?]].
      move: (Par_Abs_inv Par4) => [A'2 [a'2 ?]].
      split_hyp; subst; invert_equality; subst.
      exists (open a'2 b').
      pick fresh x. repeat spec x. split_hyp.
      split.
      eapply open2; eauto using Par_uniq, Par_lc1, Par_lc2.
      eapply open2; eauto using Par_uniq, Par_lc1, Par_lc2.
  - (* beta / app cong *)
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    subst;
    try done.
     (* rel *)
     + use_size_induction a0 a0c Par1 Par2.
       use_size_induction b bc Par3 Par4.
       move: (Par_Abs_inv Par1) => [A'1 [a'1 ?]]; split_hyp; subst.
       pick fresh x. repeat spec x. split_hyp.
       exists (open a'1 bc).
       split.
       eapply open2; eauto.
       eapply Par_AppBeta; eauto.
     + (* beta / app cong irrel *)
       use_size_induction a0 a0c Par1 Par2.
       move: (Par_Abs_inv Par1) => [A'1 [a'1 ?]]; split_hyp; subst.
       pick fresh x. repeat spec x. split_hyp.
       exists (open a'1 b').
       split.
       eapply open2; eauto using Par_uniq.
       eapply Par_AppBeta; eauto.
  - (* app cong / beta *)
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    subst;
    try done.
    + (* rel *)
      use_size_induction a0 a0c Par1 Par2.
      use_size_induction b bc Par3 Par4.
      move: (Par_Abs_inv Par2) => [? [a'1 ?]]; split_hyp; subst.
      pick fresh x. repeat spec x. split_hyp.
      exists (open a'1 bc).
      split.
      eapply Par_AppBeta; eauto.
      eapply open2; eauto.
    + (* irrel *)
      use_size_induction a0 a0c Par1 Par2.
      move: (Par_Abs_inv Par2) => [? [a'1 ?]]; split_hyp; subst.
      pick fresh x. repeat spec x. split_hyp.
      exists (open a'1 b').
      split.
      eapply Par_AppBeta; eauto.
      eapply open2; eauto using Par_uniq.
  - (* app cong / app cong *)
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
      match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
      subst;
      try done.
    + (* rel *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b bc Par3 Par4.
    exists (a_App ac psi1 bc).
    split; eauto. 
    +  (* irrel *)
      use_size_induction a0 ac Par1 Par2.
      exists (a_App ac psi1 b').
      split; eauto. 
  - (* lam cong / lam cong *)
    pick fresh x. 
    use_size_induction_open b1 x bc Par1 Par2.
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
      match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
      subst;
      try done.
    (* rel *)
    + use_size_induction A1 AC Par3 Par4.
      exists (a_Abs psi1 AC (close x bc)).
      split.
      exists_apply_Par x.
      exists_apply_Par x.
    + exists (a_Abs psi1 A1 (close x bc)).
      split.
      exists_apply_Par x.
      exists_apply_Par x.
  - (* Sigma cong / Sigma cong *)
    use_size_induction A1 ac Par1 Par2.
    pick fresh x.
    use_size_induction_open B1 x bc Par3 Par4.
    exists (a_WSigma psi1 ac (close x bc)).
    split; exists_apply_Par x; eauto.
  - (* two wpair *)
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    subst; try done.
    + (* rel *)
      use_size_induction a0 ac Par1 Par2.
      use_size_induction b1 bc Par3 Par4.
      exists (a_WPair ac psi1 bc).
      split. eauto. eauto.
    + (* two wpair irrel *) 
      use_size_induction b1 bc Par3 Par4.
      exists (a_WPair a3 psi1 bc).
      split. eauto. eauto.
  - (* letpair betas *)
    use_size_induction a0 ac Par1 Par2.
    pick fresh x.
    use_size_induction_open b1 x bc Par3 Par4.
    move: (Par_WPair_inv Par1) => [a'1 [b1' ?]]; split_hyp; subst.
    move: (Par_WPair_inv Par2) => [a'2 [b2' ?]]; split_hyp; subst.
    invert_equality; subst.
    exists (a_App (open (close x bc) a'2) q_Bot b2'). 
    repeat rewrite <- subst_spec.
    rewrite (subst_intro x b2); auto.
    rewrite (subst_intro x b3); auto.
    split. 
    + eapply Par_App; eauto using leq_Bot.
      eapply Par_subst3; try eassumption. 
    + eapply Par_App; eauto using Par_lc1, leq_Bot. 
      eapply Par_subst3; try eassumption. 
  - (* letpair beta / cong *)
    use_size_induction a0 ac Par1 Par2.
    pick fresh x.
    use_size_induction_open b1 x bc Par3 Par4.
    move: (Par_WPair_inv Par1) => [a'1 [b1' ?]]; split_hyp; subst.
    exists (a_App (open (close x bc) a'1) q_Bot b1'). 
    rewrite <- subst_spec.
    rewrite (subst_intro x b2); auto.
    split.
    + eapply Par_App; eauto using leq_Bot.
      eapply Par_subst3; try eassumption. 
    + rewrite subst_spec.
      exists_apply_Par x.
  - (* letpair cong / beta *)
    use_size_induction a0 ac Par1 Par2.
    pick fresh x.
    use_size_induction_open b1 x bc Par3 Par4.
    move: (Par_WPair_inv Par2) => [a'1 [b1' ?]]; split_hyp; subst.
    exists (a_App (open (close x bc) a'1) q_Bot b1'). 
    rewrite <- subst_spec.
    rewrite (subst_intro x b3); auto.
    split.
    + rewrite subst_spec.
      exists_apply_Par x.
    + eapply Par_App; eauto using leq_Bot.
      eapply Par_subst3; try eassumption. 
  - (* letpair cong / cong *)
    use_size_induction a0 ac Par1 Par2.
    pick fresh x.
    use_size_induction_open b1 x bc Par3 Par4.
    exists (a_LetPair psi1 ac (close x bc)).
    split.
    exists_apply_Par x.
    exists_apply_Par x.
  - (* SSigma *)
    use_size_induction A1 ac Par1 Par2.
    pick fresh x.
    use_size_induction_open B1 x bc Par3 Par4.
    exists (a_SSigma psi1 ac (close x bc)).
    split; exists_apply_Par x; eauto.
  - (* SPair cong / cong *)
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    subst; try done.
    +  use_size_induction a0 ac Par1 Par2.
       use_size_induction b1 bc Par3 Par4.
       exists (a_SPair ac psi1 bc).
       split. eauto. eauto.
    + (* SPair cong / cong irrel *)
    use_size_induction b1 bc Par3 Par4.
    exists (a_SPair a3 psi1 bc).
    split. eauto. eauto.
Admitted. (* need more size rules *)
(*
  - (* fst beta / fst beta *)
    admit. 
    use_size_induction a0 ac Par1 Par2.
    move: (Par_SPair_inv Par1) => [a'1 [b1' ?]]; split_hyp; subst.
    move: (Par_SPair_inv Par2) => [a'2 [b2' ?]]; split_hyp; subst.
     match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    subst; try done.
    invert_equality. subst.
    exists a'2. split. auto. auto.
  - (* fst beta / fst cong *)
    use_size_induction a0 ac Par1 Par2.
    move: (Par_SPair_inv Par1) => [a'1 [b1' ?]]; split_hyp; subst.
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end;
    subst; try done.
    exists a'1. split; eauto.
  - (* fst cong / fst beta *)
    use_size_induction a0 ac Par1 Par2.
    move: (Par_SPair_inv Par2) => [a'1 [b1' ?]]; split_hyp; subst.
    match goal with [ H : CPar ?S ?psi ?phi _ _ |- _ ] => inversion H; clear H end; subst; try done.    
    exists a'1. split; eauto.
  - (* fst cong / fst cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_Proj1 psi1 ac).
    split.  auto. auto.
  - (* snd beta / snd beta *)
    use_size_induction a0 ac Par1 Par2.
    move: (Par_SPair_inv Par1) => [a'1 [b1' ?]]; split_hyp; subst.
    move: (Par_SPair_inv Par2) => [a'2 [b2' ?]]; split_hyp; subst.
    invert_equality. subst.
    exists b2'. split. auto. auto.
  - (* snd *)
    use_size_induction a0 ac Par1 Par2.
    move: (Par_SPair_inv Par1) => [a'1 [b1' ?]]; split_hyp; subst.
    exists b1'. split; eauto.
  - (* snd cong / snd beta *)
    use_size_induction a0 ac Par1 Par2.
    move: (Par_SPair_inv Par2) => [a'1 [b1' ?]]; split_hyp; subst.
    exists b1'. split; eauto.
  - (* snd cong / snd cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_Proj2 psi1 ac).
    split.  auto. auto.
  - (* Sum cong *)
    use_size_induction A1 ac Par1 Par2.
    use_size_induction A2 bc Par3 Par4.
    exists (a_Sum ac bc).
    split. eauto. eauto.
  - (* Inj1 cong / cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_Inj1 ac). split; eauto.
  - (* inj2 cong / cong *)
    use_size_induction a0 ac Par1 Par2.
    exists (a_Inj2 ac). split; eauto.
  - (* case beta1 / beta1 *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 b1c Par3 Par4.
    use_size_induction b2 b2c Par5 Par6.
    move: (Par_Inj1_inv Par1) => [a'1 ?]; split_hyp; subst.
    move: (Par_Inj1_inv Par2) => [a'2 ?]; split_hyp; subst.
    invert_equality; subst.
    exists (a_App b1c psi1 a'2).
    split; eapply Par_App; eauto.

  - (* case beta1 / beta2 (impossible) *) 
    use_size_induction a0 ac Par1 Par2.
    move: (Par_Inj1_inv Par1) => [a'1 ?]; split_hyp; subst.
    move: (Par_Inj2_inv Par2) => [a'2 ?]; split_hyp; subst.
    invert_equality; subst.

  - (* case beta1 / cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 b1c Par3 Par4.
    use_size_induction b2 b2c Par5 Par6.
    move: (Par_Inj1_inv Par1) => [a'1 ?]; split_hyp; subst.

    exists (a_App b1c psi1 a'1).
    split. eapply Par_App; eauto.
    eapply Par_CaseBeta1; eauto.
  - (* case beta2 / beta1 *)
    use_size_induction a0 ac Par1 Par2.
    move: (Par_Inj2_inv Par1) => [a'1 ?]; split_hyp; subst.
    move: (Par_Inj1_inv Par2) => [a'2 ?]; split_hyp; subst.
    invert_equality; subst.
  - (* case beta2 / beta2 *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 b1c Par3 Par4.
    use_size_induction b2 b2c Par5 Par6.
    move: (Par_Inj2_inv Par1) => [a'1 ?]; split_hyp; subst.
    move: (Par_Inj2_inv Par2) => [a'2 ?]; split_hyp; subst.
    invert_equality; subst.
    exists (a_App b2c psi1 a'2).
    split; eapply Par_App; eauto.
  - (* case beta2 / cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 b1c Par3 Par4.
    use_size_induction b2 b2c Par5 Par6.
    move: (Par_Inj2_inv Par1) => [a'1 ?]; split_hyp; subst.
    exists (a_App b2c psi1 a'1).
    split. eapply Par_App; eauto.
    eapply Par_CaseBeta2; eauto.
  - (* case cong / beta1 *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 b1c Par3 Par4.
    use_size_induction b2 b2c Par5 Par6.
    move: (Par_Inj1_inv Par2) => [a'1 ?]; split_hyp; subst.
    exists (a_App b1c psi1 a'1).
    split. eapply Par_CaseBeta1; eauto.
    eapply Par_App; eauto.
  - (* case cong / beta2 *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 b1c Par3 Par4.
    use_size_induction b2 b2c Par5 Par6.
    move: (Par_Inj2_inv Par2) => [a'1 ?]; split_hyp; subst.
    exists (a_App b2c psi1 a'1).
    split. eapply Par_CaseBeta2; eauto.
    eapply Par_App; eauto.
  - (* case cong / cong *)
    use_size_induction a0 ac Par1 Par2.
    use_size_induction b1 b1c Par3 Par4.
    use_size_induction b2 b2c Par5 Par6.
    exists (a_Case psi1 ac b1c b2c).
    split; eauto.
Qed. *)

Lemma confluence : forall {S a psi a1}, Par S psi a a1 -> forall {a2}, Par S psi a a2 -> exists b, Par S psi a1 b /\ Par S psi a2 b.
Proof.
  intros.
  eapply confluence_size; eauto.
Qed.


