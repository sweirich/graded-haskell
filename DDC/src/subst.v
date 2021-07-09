Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels. 
Require Export Qual.weakening.
Require Export Qual.uniq.

Set Implicit Arguments.
Open Scope grade_scope.


(* ----- Step ----- *)

Lemma Step_substitution : forall b1 b2 a x, Step b1 b2 -> lc_tm a -> Step (subst_tm_tm a x b1) (subst_tm_tm a x b2).
Proof.
  intros. induction H.
  all: try solve [simpl; econstructor; eauto using subst_tm_tm_lc_tm]. 
  - simpl.
    rewrite subst_tm_tm_open_tm_wrt_tm; auto.
     econstructor; eauto using subst_tm_tm_lc_tm.
     inversion H. subst.
     pick fresh y.
     eapply (lc_a_Abs_exists y). 
     replace (a_Var_f y) with (subst_tm_tm a x (a_Var_f y)).
     rewrite <- subst_tm_tm_open_tm_wrt_tm; auto.
     eapply subst_tm_tm_lc_tm; eauto.
     rewrite subst_tm_tm_var_neq; auto.
  - simpl.
    econstructor; eauto using subst_tm_tm_lc_tm.
    inversion H. subst.
     pick fresh y.
     eapply (lc_a_LetPair_exists y); eauto using subst_tm_tm_lc_tm.
     replace (a_Var_f y) with (subst_tm_tm a x (a_Var_f y)).
     rewrite <- subst_tm_tm_open_tm_wrt_tm; auto.
     eapply subst_tm_tm_lc_tm; eauto.
     rewrite subst_tm_tm_var_neq; auto.
  - simpl.
    rewrite subst_tm_tm_open_tm_wrt_tm; auto.
    econstructor; eauto using subst_tm_tm_lc_tm.
    inversion H. subst.
     pick fresh y.
     eapply (lc_a_LetPair_exists y); eauto using subst_tm_tm_lc_tm.
     replace (a_Var_f y) with (subst_tm_tm a x (a_Var_f y)).
     rewrite <- subst_tm_tm_open_tm_wrt_tm; auto.
     eapply subst_tm_tm_lc_tm; eauto.
     rewrite subst_tm_tm_var_neq; auto.
Qed.


(* --- grade --- *)

Lemma Grade_CGrade: forall P phi psi a,  Grade P phi a -> CGrade P phi psi a.
Proof.
  intros.
  destruct (q_leb psi phi) eqn:LE.
  eapply CG_Leq; eauto. 
  eapply CG_Nleq; eauto using Grade_lc. rewrite LE. done.
Qed.

Local Hint Resolve Grade_CGrade : core.

Ltac substitution_ih :=
    match goal with 
      | [H3 : forall P3 x0 phi0 P4,
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 ~= P3 ++ [(x0, phi0)] ++ P4 -> _ |- _ ] => 
        specialize (H3 ([(y, psi0)] ++ P2) x phi P1 ltac:(auto));
        simpl_env in H3;
    rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto using CGrade_lc;
    rewrite subst_tm_tm_var_neq in H3
    end.

Lemma Grade_substitution_CGrade : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> CGrade P1 psi phi a 
    -> Grade (P2 ++ P1) psi (subst_tm_tm a x b).
Proof. 
  intros.
  dependent induction H.
  all: try solve [simpl; eauto].
  all: try solve [simpl; eapply_GradeIrrel; eauto using subst_tm_tm_lc_tm, CGrade_lc].
  all: try solve [simpl;
    fresh_apply_Grade y;
    eauto;
    repeat spec y;
    substitution_ih;
    eauto].
  - (* Var *) 
    destruct (x == x0).
    + subst.
      apply binds_mid_eq in H1; auto. subst.
      rewrite subst_tm_tm_var; auto.
      eapply Grade_weakening; try solve_uniq.
      match goal with [ H : CGrade _ _ _ _ |- _ ] => inversion H; clear H; subst end; auto; try done.
    + rewrite subst_tm_tm_var_neq. auto.
      apply binds_remove_mid in H1; auto.
      eapply G_Var; eauto.
Qed.

Lemma Grade_substitution_same : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> Grade P1 psi a 
    -> Grade (P2 ++ P1) psi (subst_tm_tm a x b).
Proof. 
  intros.
  eapply Grade_substitution_CGrade; eauto.
Qed.
  
Lemma Grade_substitution_irrel : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> not (phi <= psi)
    -> lc_tm a
    -> Grade (P2 ++ P1) psi (subst_tm_tm a x b).
Proof. 
  intros.
  eapply Grade_substitution_CGrade; eauto.
Qed.

Lemma Grade_open : forall P psi y psi0 a b,
  y `notin` fv_tm_tm a ->
  Grade P psi b ->
  Grade ([(y, psi0)] ++ P) psi (open_tm_wrt_tm a (a_Var_f y)) -> 
  Grade P psi (open_tm_wrt_tm a b).
Proof.
  intros.
  move: (Grade_substitution_same nil _ _ H1 H0) => ss.
  rewrite subst_tm_tm_open_tm_wrt_tm in ss.
  eauto using Grade_lc.
  rewrite subst_tm_tm_var in ss.
  rewrite subst_tm_tm_fresh_eq in ss; auto.
Qed.

Lemma Grade_open_irrel : forall P psi y psi0 a b,
  y `notin` fv_tm_tm a ->
  not (psi0 <= psi) ->
  lc_tm b ->
  Grade ([(y, psi0)] ++ P) psi (open_tm_wrt_tm a (a_Var_f y)) -> 
  Grade P psi (open_tm_wrt_tm a b).
Proof.
  intros.
  move: (Grade_substitution_irrel nil _ _ H2 ltac:(auto) H1) => ss.
  rewrite subst_tm_tm_open_tm_wrt_tm in ss.
  eauto using Grade_lc.
  rewrite subst_tm_tm_var in ss.
  rewrite subst_tm_tm_fresh_eq in ss; auto.
Qed.

Lemma Grade_renaming : forall y x psi0 P psi b1, 
    x `notin` dom P \u fv_tm_tm b1 -> 
    y `notin` dom P \u fv_tm_tm b1 \u {{x}} -> 
    Grade ([(y, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f y)) -> 
    Grade ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_tm_tm_intro y b1); auto.
  move: (Grade_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply Grade_substitution_same with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env.
    eapply Grade_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply Grade_substitution_irrel  with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env. 2: eauto.
    eapply Grade_weakening_middle; eauto. 
    rewrite LE. done.
    auto.
Qed. 

Ltac exists_apply_Grade x :=
  let y := fresh in
  fresh_apply_Grade y; eauto;
  eapply (@Grade_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.

(* --- geq --- *)

Lemma CEq_GEq_equality_substitution : 
  (forall P phi phi0 b1 b2,
  CEq P phi phi0 b1 b2 ->  forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a1 a2, CEq P1 phi psi a1 a2 
       -> CEq (P2 ++ P1) phi phi0 (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2)) /\
  (forall P phi b1 b2,
  GEq P phi b1 b2 -> forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a1 a2, CEq P1 phi psi a1 a2  
       -> GEq (P2 ++ P1) phi (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2)). 
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; subst; eauto.  
  all: try solve [simpl; eauto].
  all: try solve [
    repeat invert_Grade; subst;
    simpl; fresh_apply_GEq y; eauto;
    repeat spec y;
    match goal with 
      [ 
         H5 : forall P3 P4 x0 psi1,  
          [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?psi2)] ++ ?P1 = P4 ++ [(x0, psi1)] ++ P3 -> _ 
          |- _ ] => 
    specialize (H5 P1 ([(y, psi0)] ++ P2) x psi2 ltac:(auto) _ _ ltac:(eauto 3));
    simpl_env in H5;
    simpl_env in H5;
    repeat rewrite subst_tm_tm_open_tm_wrt_tm in H5; eauto 3 using CEq_lc1, CEq_lc2;
    repeat rewrite subst_tm_tm_var_neq in H5; eauto
    end] .
  - (* Var *)
    destruct (x == x0).
    + subst.
      repeat rewrite subst_tm_tm_var.
      match goal with [ H : CEq _ _ _ _ _ |- _ ] => inversion H; subst end.
      ++ (* 
            psi0 <= psi -- 
          *)
        eapply GEq_weakening; eauto.        
      ++
        apply binds_mid_eq in b; auto. subst.
        done.
        (* 
            here we know that not (psi0 <= psi). 
          *)
    + repeat rewrite subst_tm_tm_var_neq; eauto.    

  - (* CEq  - nleq *)
    move: (CEq_lc1 H0) => h1.
    move: (CEq_lc2 H0) => h2.
    eapply CEq_Nleq; eauto using subst_tm_tm_lc_tm.
Qed.


Lemma GEq_open: forall P psi psi0 a1 a2 a b0 x, 
      x \notin fv_tm_tm a -> x \notin fv_tm_tm b0 ->
      CEq P psi psi0 a1 a2 ->
      GEq ([(x, psi0)] ++ P) psi (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm b0 (a_Var_f x)) ->
      GEq P psi (open_tm_wrt_tm a a1) (open_tm_wrt_tm b0 a2).
Proof.
      intros.
      move: (CEq_GEq_equality_substitution) => [_ h1].
      specialize (h1 _ _  _ _ H2 P nil x psi0 ltac:(eauto) _ _ H1).
      repeat rewrite subst_tm_tm_open_tm_wrt_tm in h1; auto.
      eapply CEq_lc1; eauto.
      eapply CEq_lc2; eauto.
      repeat rewrite subst_tm_tm_var in h1.
      repeat rewrite subst_tm_tm_fresh_eq in h1; auto.
Qed.

Lemma GEq_refl : forall P phi a, Grade P phi a -> GEq P phi a a.
Proof. 
  induction 1; intros; eauto.
  - eapply GEq_App; eauto.
    destruct (q_leb psi0 psi) eqn:L.
    unfold is_true in H1. done.
    eapply CEq_Nleq; eauto using Grade_lc, Grade_uniq. 
  - eapply GEq_WPair; eauto.
    destruct (q_leb psi0 psi) eqn:L.
    unfold is_true in H1. done.
    eapply CEq_Nleq; eauto using Grade_lc, Grade_uniq. 
  - eapply GEq_SPair; eauto.
    destruct (q_leb psi0 psi) eqn:L.
    unfold is_true in H1. done.
    eapply CEq_Nleq; eauto using Grade_lc, Grade_uniq. 
Qed.

Lemma CEq_refl : forall P phi a psi, Grade P phi a -> CEq P phi psi a a.
Proof.
  intros.
  destruct (q_leb psi phi) eqn:LE.
  + eapply CEq_Leq; eauto.
    eapply GEq_refl; eauto.
  + eapply CEq_Nleq; eauto using Grade_uniq, Grade_lc.
    rewrite LE. done.
Qed.


Lemma GEq_substitution_same : forall P1 P2 x psi phi b1 b2 a,
  GEq (P2 ++ [(x,psi)] ++ P1) phi b1 b2 
  -> Grade P1 phi a
  -> GEq (P2 ++ P1) phi (subst_tm_tm a x b1) (subst_tm_tm a x b2). 
Proof.
  intros.
  move: CEq_GEq_equality_substitution => [_ h].
  eapply h; eauto.
  eapply CEq_refl; auto.
Qed.

Lemma GEq_substitution_irrel : forall P1 P2 x psi phi b1 b2 a1 a2,
  GEq (P2 ++ [(x,psi)] ++ P1) phi b1 b2 
  -> not (psi <= phi)
  -> lc_tm a1
  -> lc_tm a2
  -> GEq (P2 ++ P1) phi (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2). 
Proof.
  intros.
  move: CEq_GEq_equality_substitution => [_ h].
  eapply h; eauto.
  eapply CEq_Nleq; eauto.
  move: (GEq_uniq H) => u. solve_uniq.
Qed.

Lemma GEq_renaming : forall y x psi0 P psi b1 b2, 
    x `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 -> 
    y `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 \u {{x}} -> 
    GEq ([(y, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y)) -> 
    GEq ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_tm_tm_intro y b1); auto.
  rewrite (subst_tm_tm_intro y b2); auto.
  move: (GEq_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply GEq_substitution_same with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env.
    eapply GEq_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply GEq_substitution_irrel  with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); auto; simpl_env. 
    eapply GEq_weakening_middle; eauto. 
    rewrite LE. done.
Qed. 

Ltac exists_apply_GEq x :=
  let y := fresh in
  fresh_apply_GEq y; eauto;
  eapply (@GEq_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.


(* --- defeq ---- *)

Local Ltac defeq_subst_ih :=  match goal with 
      [ 
         H5 : forall P3 P4 x0 psi1,  
          [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?psi2)] ++ ?P1 = P4 ++ [(x0, psi1)] ++ P3 -> _ 
          |- _ ] => 
    specialize (H5 P1 ([(y, psi0)] ++ P2) x psi2 ltac:(auto) _ ltac:(eauto 3));
    simpl_env in H5;
    repeat rewrite subst_tm_tm_open_tm_wrt_tm in H5; eauto 3 using CGrade_lc;
    repeat rewrite subst_tm_tm_var_neq in H5; eauto end.

Lemma DefEq_substitution_CGrade : 
  (forall P phi b1 b2, DefEq P phi b1 b2 -> forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a, CGrade P1 phi psi a
       -> DefEq (P2 ++ P1) phi (subst_tm_tm a x b1) (subst_tm_tm a x b2)). 
Proof. 
  intros P phi b1 b2 h. induction h.
  all: intros; subst.  
  all: try solve [eapply Eq_Refl; eauto using Grade_substitution_CGrade].
  all: try solve [eapply Eq_Beta; eauto using Grade_substitution_CGrade, Step_substitution, CGrade_lc].
  all: try solve [simpl; eapply Eq_AppIrrel; eauto using Grade_substitution_CGrade, subst_tm_tm_lc_tm, CGrade_lc].
  all: try solve [simpl; eapply Eq_WPairIrrel; eauto using Grade_substitution_CGrade, subst_tm_tm_lc_tm, CGrade_lc].
  all: try solve [simpl; eapply Eq_SPairIrrel; eauto using Grade_substitution_CGrade, subst_tm_tm_lc_tm, CGrade_lc].
  all: try solve [repeat invert_Grade; subst;
    simpl; fresh_apply_DefEq y; eauto 2;
    repeat spec y;
    defeq_subst_ih] .
  all: try solve [simpl; eauto 3].
  eapply Eq_Trans; eauto 2.
  all: try solve [simpl; eauto 4 using Grade_substitution_CGrade, Step_substitution, CGrade_lc].
  - eapply Eq_PiFst; eauto 1. 
    specialize (IHh _ _ _ _ ltac:(eauto) _ ltac:(eauto));
    simpl in IHh; eauto.
  - repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc.
    match goal with [H0 : CGrade _ _ _ _|- _ ] => 
    specialize (IHh2 _ _ _ _ ltac:(eauto) _ H0);
    specialize (IHh1 _ _ _ _ ltac:(eauto) _ H0) end. simpl in IHh1.
    eapply Eq_PiSnd; eauto 3 using Grade_substitution_CGrade, subst_tm_tm_lc_tm, CGrade_lc.    
  - repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc.
    specialize (IHh _ _ _ _ ltac:(eauto) _ H0); simpl in IHh; eauto.
  - repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc.
    specialize (IHh _ _ _ _ ltac:(eauto) _ H1); simpl in IHh.
    eapply Eq_WSigmaSnd; eauto using Grade_substitution_CGrade.
  - specialize (IHh _ _ _ _ ltac:(eauto) _ H0); simpl in IHh.
    eapply Eq_SSigmaFst; eauto using Grade_substitution_CGrade.
  - repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc.
    specialize (IHh1 _ _ _ _ ltac:(eauto) _ H0); simpl in IHh1.
    eapply Eq_SSigmaSnd; eauto using Grade_substitution_CGrade.
  - eapply Eq_SumFst; eauto 1.  
    specialize (IHh _ _ _ _ ltac:(eauto) _ ltac:(eauto));
    simpl in IHh; eauto.
  - eapply Eq_SumSnd; eauto 1.  
    specialize (IHh _ _ _ _ ltac:(eauto) _ ltac:(eauto));
    simpl in IHh; eauto.
  - simpl.
    eapply Eq_Case; eauto.
  - repeat invert_Grade; subst;
    simpl.
    repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using CGrade_lc.
    pick fresh y and apply Eq_SubstIrrel; eauto 2. 
    eauto using subst_tm_tm_lc_tm, CGrade_lc.    
    eauto using subst_tm_tm_lc_tm, CGrade_lc.    
    repeat spec y.
    specialize (H3 P1 ([(y, psi)] ++ P2) x psi0).
    simpl_env in H3. specialize (H3 ltac:(auto)).
    specialize (H3 _ ltac:(eassumption)).
    repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto 2 using CGrade_lc.
    rewrite subst_tm_tm_var_neq in H3. auto.
    auto.
Qed.

Lemma DefEq_substitution_same : 
  (forall P phi b1 b2, DefEq P phi b1 b2 -> forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a, Grade P1 phi a
       -> DefEq (P2 ++ P1) phi (subst_tm_tm a x b1) (subst_tm_tm a x b2)). 
Proof. 
  intros.
  eapply DefEq_substitution_CGrade; eauto.
Qed.

Lemma DefEq_substitution_irrel : forall (P : econtext) (psi : grade) (b1 b2 : tm),
       DefEq P psi b1 b2 ->
       forall (P1 P2 : list (atom * grade)) (x : atom) (phi : grade),
       P = P2 ++ [(x, phi)] ++ P1 ->
       not (phi <= psi) ->
       forall a : tm, lc_tm a -> DefEq (P2 ++ P1) psi (subst_tm_tm a x b1) (subst_tm_tm a x b2).
Proof. 
  intros.
  eapply DefEq_substitution_CGrade; eauto.
Qed.


Lemma DefEq_renaming : forall y x psi0 P psi b1 b2, 
    x `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 -> 
    y `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 \u {{x}} -> 
    DefEq ([(y, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y)) -> 
    DefEq ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_tm_tm_intro y b1); auto.
  rewrite (subst_tm_tm_intro y b2); auto.
  move: (DefEq_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply DefEq_substitution_same with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env. 2: eauto.
    eapply DefEq_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply DefEq_substitution_irrel  with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env. 2: eauto.
    eapply DefEq_weakening_middle; eauto. 
    rewrite LE. done.
    auto.
Qed. 

Ltac exists_apply_DefEq x :=
  let y := fresh in
  fresh_apply_DefEq y; eauto;
  eapply (@DefEq_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.


(* --- par ---- *)


Local Ltac par_subst2_ih :=
    match goal with 
      | [H3 : forall P3 x0 phi0 P4,
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 ~= P3 ++ [(x0, phi0)] ++ P4 -> _ |- _ ] => 
    specialize (H3 ([(y, psi0)] ++ P2) x phi P1 ltac:(reflexivity) _ ltac:(eassumption));
    simpl_env in H3;
    repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto 3 using CGrade_lc, Par_lc1, Par_lc2;
    repeat rewrite subst_tm_tm_var_neq in H3 
    end.

Lemma Par_substitution_CGrade : forall P2 x phi P1 psi a a', 
  Par (P2 ++ [(x, phi)] ++ P1) psi a a' -> 
  forall b, CGrade P1 psi phi b ->
  Par (P2 ++ P1) psi (subst_tm_tm b x a) (subst_tm_tm b x a').
Proof.
  intros P2 x phi P1 psi a a' PAR.
  dependent induction PAR; simpl; intros.
  all: simpl; eauto using Grade_substitution_CGrade, GEq_substitution_same, GEq_substitution_irrel.
  (* 13 subgoals *)
  all: repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto using CGrade_lc.
  all: try solve [fresh_apply_Par y; eauto; repeat spec y;
            par_subst2_ih; eauto].
  (* 6 subgoals *)
  all: try (eapply_ParIrrel; eauto using CGrade_lc, subst_tm_tm_lc_tm).
  - eapply Par_Proj1Beta; eauto using CGrade_lc, subst_tm_tm_lc_tm.
    simpl in IHPAR. eauto.
  - eapply Par_Proj2Beta; eauto using CGrade_lc, subst_tm_tm_lc_tm.
    simpl in IHPAR. eauto.
Qed.


Lemma subst2 : forall x phi P1 psi a a' b, 
  Par ([(x, phi)] ++ P1) psi a a' -> 
  Grade P1 psi b ->
  Par P1 psi (subst_tm_tm b x a) (subst_tm_tm b x a').
Proof. intros. eapply Par_substitution_CGrade with (P2:=nil); eauto. Qed.

Lemma subst2_irrel : forall x phi P1 psi a a', 
  Par ([(x, phi)] ++ P1) psi a a' -> 
  forall b, not (phi <= psi) ->
  lc_tm b ->
  Par P1 psi (subst_tm_tm b x a) (subst_tm_tm b x a').
Proof.
  intros.
  eapply Par_substitution_CGrade with (P2:=nil); eauto. Qed.

Lemma Par_renaming : forall y x psi0 P psi b1 b2, 
    x `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 -> 
    y `notin` dom P \u fv_tm_tm b1 \u fv_tm_tm b2 \u {{x}} -> 
    Par ([(y, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f y)) (open_tm_wrt_tm b2 (a_Var_f y)) -> 
    Par ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_tm_tm_intro y b1); auto.
  rewrite (subst_tm_tm_intro y b2); auto.
  move: (Par_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply subst2; eauto.
    eapply Par_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply subst2_irrel; eauto.
    eapply Par_weakening_middle; eauto. 
    rewrite LE. done.
Qed. 

Ltac exists_apply_Par x :=
  let y := fresh in
  fresh_apply_Par y; eauto;
  eapply (@Par_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.

(* Par / CPar substitution *)

Local Ltac subst5_ih :=
    match goal with 
      | [H3 : forall P3 P4 x0 phi0,
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 ~= P4 ++ [(x0, phi0)] ++ P3 -> _ |- _ ] => 
    specialize (H3 P1 ([(y, psi0)] ++ P2) x phi ltac:(reflexivity) _ _ ltac:(eassumption));
    simpl_env in H3;
    repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2;
    repeat rewrite subst_tm_tm_var_neq in H3 
    end.

Lemma subst5_full :
 (forall P psi psi0 a a',
  CEq P psi psi0 a a' ->  forall P1 P2 x phi,
        P = P2 ++ [(x,phi)] ++ P1 
       -> psi0 <= psi -> forall b b', CPar P1 psi phi b b' 
       -> Par (P2 ++ P1) psi (subst_tm_tm b x a) (subst_tm_tm b' x a')) /\
  (forall P psi a a',
  GEq P psi a a' -> forall P1 P2 x phi, 
        P = P2 ++ [(x,phi)] ++ P1 
       -> forall b b', CPar P1 psi phi b b' 
       -> Par (P2 ++ P1) psi (subst_tm_tm b x a) (subst_tm_tm b' x a')).
Proof.
  eapply CEq_GEq_mutual.
  all: intros; subst; simpl; eauto.  

  destruct (x == x0); subst;
  [  inversion H0; subst; eapply Par_weakening; eauto;
    apply binds_mid_eq in b; auto; subst; done
  | eauto].

  all : try solve [
  fresh_apply_Par y; eauto 3; repeat spec y;
  match goal with 
      | [H3 : forall P3 P4 x0 phi0,
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 = P4 ++ [(x0, phi0)] ++ P3 -> _ |- _ ] => 
    specialize (H3 P1 ([(y, psi0)] ++ P2) x phi ltac:(reflexivity) _ _ ltac:(eassumption));
    simpl_env in H3;
    repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2;
    repeat rewrite subst_tm_tm_var_neq in H3 end; eauto 3 ].

  all: destruct (q_leb psi0 psi) eqn:LE; try done.
  eapply Par_AppRel; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2, subst_tm_tm_lc_tm.
  eapply Par_AppIrrel; eauto 4 using Grade_lc, CPar_lc1, CPar_lc2, CEq_lc1, CEq_lc2, subst_tm_tm_lc_tm.
  rewrite LE. done.

  eapply Par_WPairRel; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2, subst_tm_tm_lc_tm.
  eapply Par_WPairIrrel; eauto 4 using Grade_lc, CPar_lc1, CPar_lc2, CEq_lc1, CEq_lc2, subst_tm_tm_lc_tm.
  rewrite LE. done.

  eapply Par_SPairRel; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2, subst_tm_tm_lc_tm.
  eapply Par_SPairIrrel; eauto 4 using Grade_lc, CPar_lc1, CPar_lc2, CEq_lc1, CEq_lc2, subst_tm_tm_lc_tm.
  rewrite LE. done.
Qed.




Lemma Par_subst3_full : forall P2 phi P1 b psi b' x,
    CPar P1 psi phi b b' ->
    forall a a', Par (P2 ++ [(x,phi)] ++ P1) psi a a' ->
    Par (P2 ++ P1) psi (subst_tm_tm b x a) (subst_tm_tm b' x a').
Proof.
  intros.
  dependent induction H0; simpl; eauto 4.


  (* refl case *)
  move: (subst5_full) => [_ h]. 
  eapply h; eauto using GEq_refl.

  all: repeat rewrite subst_tm_tm_open_tm_wrt_tm; eauto 2 using  CPar_lc1, CPar_lc2.
  all: eauto.
  all: try (eapply_ParIrrel; eauto 3 using CPar_lc1, CPar_lc2, subst_tm_tm_lc_tm).  

  all: try solve [
  fresh_apply_Par y; eauto 3; repeat spec y;
  match goal with 
      | [H3 : forall P3 phi0 P4 x0,
            CPar P4 ?psi ?phi0 ?b ?b' ->
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 ~= P3 ++ [(x0, phi0)] ++ P4 -> _ |- _ ] => 
    specialize (H3  ([(y, psi0)] ++ P2) phi P1 x ltac:(eassumption) ltac:(reflexivity));
    simpl_env in H3;
    repeat rewrite subst_tm_tm_open_tm_wrt_tm in H3; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2;
    repeat rewrite subst_tm_tm_var_neq in H3 end; eauto 3].

  eapply Par_Proj1Beta; eauto.
  eapply IHPar; eauto.

  eapply Par_Proj2Beta; eauto.
  eapply IHPar; eauto.
Qed.

Lemma Par_subst3 : forall P1 phi b psi b' x,
    CPar P1 psi phi b b' ->
    forall a a', Par ([(x,phi)] ++ P1) psi a a' ->
    Par P1 psi (subst_tm_tm b x a) (subst_tm_tm b' x a').
Proof.
  intros.
  eapply Par_subst3_full with (P2 := nil); eauto.
Qed.

(* --------------------------- *)
