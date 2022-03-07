Require Export ssreflect.
Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels. 
Require Export Qual.weakening.
Require Export Qual.uniq.

Set Implicit Arguments.
Open Scope grade_scope.

#[local] Opaque Syntax_tm.
#[local] Opaque Subst_tm.


(* ----- Step ----- *)

Lemma Step_substitution : forall b1 b2 a x, Step b1 b2 -> lc a -> Step (subst a x b1) (subst a x b2).
Proof.
  intros. induction H.
  all: try solve [simpl; econstructor; eauto using subst_lc with syntax]. 
  - simp_syntax. 
    (* why does simpl unfold the type class here. How to prevent that? *)
    rewrite subst_open; auto.
    econstructor; eauto using subst_lc.
    pose proof (K := subst_lc (a_Abs psi A a0) a x).
    eauto.
    (* why does move not work here? *)
Admitted.
(*  - simp_syntax.
    econstructor; eauto using subst_lc.
    inversion H. subst.
     pick fresh y.
     eapply (lc_a_LetPair_exists y); eauto using subst_lc.
     replace (a_Var_f y) with (subst a x (a_Var_f y)).
     rewrite <- subst_open; auto.
     eapply subst_lc; eauto.
     rewrite subst_var_neq; auto.
  - simp_syntax.
    rewrite subst_open; auto.
    econstructor; eauto using subst_lc.
    inversion H. subst.
     pick fresh y.
     eapply (lc_a_LetPair_exists y); eauto using subst_lc.
     replace (a_Var_f y) with (subst a x (a_Var_f y)).
     rewrite <- subst_open; auto.
     eapply subst_lc; eauto.
     rewrite subst_var_neq; auto.
Qed. *)


(* --- grade --- *)

Lemma Grade_CGrade: forall P phi psi a,  Grade P phi a -> CGrade P phi psi a.
Proof.
  intros.
  destruct (q_leb psi phi) eqn:LE.
  eapply CG_Leq; eauto. 
  eapply CG_Nleq; eauto using Grade_uniq, Grade_lc. rewrite LE. done.
Qed.

Local Hint Resolve Grade_CGrade : core.

Ltac substitution_ih :=
    match goal with 
      | [H3 : forall P4 P3 x0 phi0,
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 = P3 ++ [(x0, phi0)] ++ P4 -> _ |- _ ] => 
                specialize (H3 P1 ([(y, psi0)] ++ P2) x phi  ltac:(auto) _ ltac:(eauto)); 
        simpl_env in H3;
    rewrite subst_open in H3; eauto using CGrade_lc;
    rewrite subst_var_neq in H3
    end.

Lemma CGrade_Grade_substitution_CGrade : (forall P psi psi0 b,
      CGrade P psi psi0 b -> forall P1 P2 x phi, 
        P = P2 ++ [(x,phi)] ++ P1 
        -> forall a , CGrade P1 psi phi a 
        -> CGrade (P2 ++ P1) psi psi0 (subst a x b)) /\
      (forall P psi b, 
          Grade P psi b -> forall P1 P2 x phi, 
            P = P2 ++ [(x,phi)] ++ P1 
            -> forall a, CGrade P1 psi phi a 
                   -> Grade (P2 ++ P1) psi (subst a x b)).
Proof.
  apply CGrade_Grade_mutual. 
  all: intros; subst.
  all: try solve [simpl; eauto].
  all: try solve [eapply CG_Nleq; eauto  using subst_lc, CGrade_lc] .
  all: try solve [simpl;
    fresh_apply_Grade y;
    eauto using subst_lc, CGrade_lc;
    repeat spec y;
    substitution_ih;
    eauto].
  - (* Var *) 
    substitution_var.
    + eapply Grade_weakening; try solve_uniq.
      invert_CGrade; subst; auto; try done.
    + eapply G_Var; eauto.
Qed.

Lemma Grade_substitution_CGrade : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> CGrade P1 psi phi a 
    -> Grade (P2 ++ P1) psi (subst a x b).
Proof. 
  intros.
  eapply CGrade_Grade_substitution_CGrade; eauto. Qed.

#[global] Hint Resolve Grade_substitution_CGrade : subst.

Lemma Grade_substitution_same : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> Grade P1 psi a 
    -> Grade (P2 ++ P1) psi (subst a x b).
Proof. 
  intros.
  eapply Grade_substitution_CGrade; eauto.
Qed.
  
Lemma Grade_substitution_irrel : forall P2 x phi P1 psi a b,
      Grade (P2 ++ x ~ phi ++ P1) psi b
    -> not (phi <= psi)
    -> lc a
    -> Grade (P2 ++ P1) psi (subst a x b).
Proof. 
  intros.
  eapply Grade_substitution_CGrade; eauto.
  eapply Grade_uniq in H. destruct_uniq.
  eauto.
Qed.

Lemma Grade_open : forall P psi y psi0 a b,
  y `notin` fv a ->
  Grade P psi b ->
  Grade ([(y, psi0)] ++ P) psi (open a (a_Var_f y)) -> 
  Grade P psi (open a b).
Proof.
  intros.
  move: (Grade_substitution_same nil _ _ H1 H0) => ss.
  rewrite subst_open in ss.
  eauto using Grade_lc.
  rewrite subst_var in ss.
  rewrite subst_fresh_eq in ss; auto.
Qed.

Lemma Grade_open_irrel : forall P psi y psi0 a b,
  y `notin` fv a ->
  not (psi0 <= psi) ->
  lc b ->
  Grade ([(y, psi0)] ++ P) psi (open a (a_Var_f y)) -> 
  Grade P psi (open a b).
Proof.
  intros.
  move: (Grade_substitution_irrel nil _ _ H2 ltac:(auto) H1) => ss.
  rewrite subst_open in ss.
  eauto using Grade_lc.
  rewrite subst_var in ss.
  rewrite subst_fresh_eq in ss; auto.
Qed.

Lemma Grade_renaming : forall y x psi0 P psi b1, 
    x `notin` dom P \u fv b1 -> 
    y `notin` dom P \u fv b1 \u {{x}} -> 
    Grade ([(y, psi0)] ++ P) psi (open b1 (a_Var_f y)) -> 
    Grade ([(x, psi0)] ++ P) psi (open b1 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_intro y b1); auto.
  move: (Grade_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply Grade_substitution_same with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env.
    eapply Grade_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply Grade_substitution_irrel  with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env. 
    eapply Grade_weakening_middle; eauto. 
    rewrite LE. done.
    eauto with lc.
Qed. 

Ltac exists_apply_Grade x :=
  let y := fresh in
  fresh_apply_Grade y; eauto;
  eapply (@Grade_renaming x); try rewrite fv_close; auto;
  rewrite open_close; auto.

(* --- geq --- *)

Lemma CEq_GEq_equality_substitution : 
  (forall P phi phi0 b1 b2,
  CEq P phi phi0 b1 b2 ->  forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a1 a2, CEq P1 phi psi a1 a2 
       -> CEq (P2 ++ P1) phi phi0 (subst a1 x b1) (subst a2 x b2)) /\
  (forall P phi b1 b2,
  GEq P phi b1 b2 -> forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a1 a2, CEq P1 phi psi a1 a2  
       -> GEq (P2 ++ P1) phi (subst a1 x b1) (subst a2 x b2)). 
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
    repeat rewrite subst_open in H5; eauto 3 using CEq_lc1, CEq_lc2;
    repeat rewrite subst_var_neq in H5; eauto
    end] .
  - (* Var *)
    substitution_var. 
    + invert_CEq; subst.      
      eapply GEq_weakening; eauto.        
      done.
    + eauto.    
  - (* CEq  - nleq *)
    move: (CEq_lc1 H0) => h1.
    move: (CEq_lc2 H0) => h2.
    eapply CEq_Nleq; eauto using subst_lc.
Qed.

Lemma GEq_substitution : forall P1 P2 x psi phi b1 b2,
  GEq (P2 ++ [(x,psi)] ++ P1) phi b1 b2
       -> forall a1 a2, CEq P1 phi psi a1 a2  
       -> GEq (P2 ++ P1) phi (subst a1 x b1) (subst a2 x b2). 
Proof. intros; subst. eapply CEq_GEq_equality_substitution; eauto. Qed.

Lemma GEq_open: forall P psi psi0 a1 a2 a b0 x, 
      x \notin fv a -> x \notin fv b0 ->
      CEq P psi psi0 a1 a2 ->
      GEq ([(x, psi0)] ++ P) psi (open a (a_Var_f x)) (open b0 (a_Var_f x)) ->
      GEq P psi (open a a1) (open b0 a2).
Proof.
      intros.
      move: (CEq_GEq_equality_substitution) => [_ h1].
      specialize (h1 _ _  _ _ H2 P nil x psi0 ltac:(eauto) _ _ H1).
      repeat rewrite subst_open in h1; auto.
      eapply CEq_lc1; eauto.
      eapply CEq_lc2; eauto.
      repeat rewrite subst_var in h1.
      repeat rewrite subst_fresh_eq in h1; auto.
Qed.

Lemma CEq_GEq_refl : 
  (forall P phi psi a, CGrade P phi psi a -> CEq P phi psi a a) /\
  (forall P phi a, Grade P phi a -> GEq P phi a a).
Proof. 
  eapply CGrade_Grade_mutual.
  all: intros; eauto.
Qed.

Lemma GEq_refl : forall P phi a, Grade P phi a -> GEq P phi a a.
  intros. eapply CEq_GEq_refl. auto.
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
  -> GEq (P2 ++ P1) phi (subst a x b1) (subst a x b2). 
Proof.
  intros.
  move: CEq_GEq_equality_substitution => [_ h].
  eapply h; eauto.
  eapply CEq_refl; auto.
Qed.

Lemma GEq_substitution_irrel : forall P1 P2 x psi phi b1 b2 a1 a2,
  GEq (P2 ++ [(x,psi)] ++ P1) phi b1 b2 
  -> not (psi <= phi)
  -> lc a1
  -> lc a2
  -> GEq (P2 ++ P1) phi (subst a1 x b1) (subst a2 x b2). 
Proof.
  intros.
  move: CEq_GEq_equality_substitution => [_ h].
  eapply h; eauto.
  eapply CEq_Nleq; eauto.
  move: (GEq_uniq H) => u. solve_uniq.
Qed.

Lemma GEq_renaming : forall y x psi0 P psi b1 b2, 
    x `notin` dom P \u fv b1 \u fv b2 -> 
    y `notin` dom P \u fv b1 \u fv b2 \u {{x}} -> 
    GEq ([(y, psi0)] ++ P) psi (open b1 (a_Var_f y)) (open b2 (a_Var_f y)) -> 
    GEq ([(x, psi0)] ++ P) psi (open b1 (a_Var_f x)) (open b2 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_intro y b1); auto.
  rewrite (subst_intro y b2); auto.
  move: (GEq_uniq H1) => u. 
  eapply GEq_substitution with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env.
  eapply GEq_weakening_middle; eauto. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply CEq_refl.
    eapply G_Var; eauto.
    solve_uniq.
  - eapply CEq_Nleq; eauto with lc. 
    rewrite LE. done. 
    solve_uniq.
Qed. 

Ltac exists_apply_GEq x :=
  let y := fresh in
  fresh_apply_GEq y; eauto;
  eapply (@GEq_renaming x); try rewrite fv_close; auto;
  rewrite open_close; auto.


(* --- defeq ---- *)

Local Ltac defeq_subst_ih :=  match goal with 
      [ 
         H5 : forall P3 P4 x0 psi1,  
          [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?psi2)] ++ ?P1 = P4 ++ [(x0, psi1)] ++ P3 -> _ 
          |- _ ] => 
    specialize (H5 P1 ([(y, psi0)] ++ P2) x psi2 ltac:(auto) _ ltac:(eauto 3));
    simpl_env in H5;
    repeat rewrite subst_open in H5; eauto 3 using CGrade_lc;
    repeat rewrite subst_var_neq in H5; eauto end.



Lemma CDefEq_DefEq_substitution_CGrade : 
  (forall P phi phi0 b1 b2, CDefEq P phi phi0 b1 b2 -> forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a, CGrade P1 phi psi a
       -> CDefEq (P2 ++ P1) phi phi0 (subst a x b1) (subst a x b2)) /\
  (forall P phi b1 b2, DefEq P phi b1 b2 -> forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a, CGrade P1 phi psi a
       -> DefEq (P2 ++ P1) phi (subst a x b1) (subst a x b2)). 
Proof. 
  apply CDefEq_DefEq_mutual.
  all: intros; subst.  
  all: try solve [eapply Eq_Refl; eauto using Grade_substitution_CGrade].
  all: try solve [eapply Eq_Beta; eauto using Grade_substitution_CGrade, Step_substitution, CGrade_lc].
  all: try solve [simpl; eapply Eq_App; eauto using Grade_substitution_CGrade, subst_lc, CGrade_lc].
  all: try solve [simpl; eapply Eq_WPair; eauto using Grade_substitution_CGrade, subst_lc, CGrade_lc].
  all: try solve [simpl; eapply Eq_SPair; eauto using Grade_substitution_CGrade, subst_lc, CGrade_lc].
  all: try solve [repeat invert_Grade; subst;
    simpl; fresh_apply_DefEq y; eauto 3 using subst_lc, CGrade_lc;
    repeat spec y;
    defeq_subst_ih] .
  all: try solve [simpl; eauto 3].
  eapply Eq_Trans; eauto 2.
  all: try solve [simpl; eauto 4 using Grade_substitution_CGrade, Step_substitution, CGrade_lc].
  - eapply Eq_PiFst; eauto 1. 
    specialize (H _ _ _ _ ltac:(eauto) _ ltac:(eauto));
    simpl in H; eauto.
  - repeat rewrite subst_open; eauto 2 using CGrade_lc.
    match goal with [H2 : CGrade _ _ _ _|- _ ] => 
    specialize (H0 _ _ _ _ ltac:(eauto) _ H2);
    specialize (H _ _ _ _ ltac:(eauto) _ H2) end. 
    autorewrite with subst in H.
    eapply Eq_PiSnd; eauto 3 using Grade_substitution_CGrade, subst_lc, CGrade_lc.    
  - repeat rewrite subst_open; eauto 2 using CGrade_lc.
    specialize (H _ _ _ _ ltac:(eauto) _ H1); simpl in H; eauto.
  - repeat rewrite subst_open; eauto 2 using CGrade_lc.
    specialize (H _ _ _ _ ltac:(eauto) _ H1); simpl in H.
    eapply Eq_WSigmaSnd; eauto using Grade_substitution_CGrade.
  - specialize (H _ _ _ _ ltac:(eauto) _ H1); simpl in H.
    eapply Eq_SSigmaFst; eauto using Grade_substitution_CGrade.
  - repeat rewrite subst_open; eauto 2 using CGrade_lc.
    specialize (H _ _ _ _ ltac:(eauto) _ H2); simpl in H.
    eapply Eq_SSigmaSnd; eauto using Grade_substitution_CGrade.
  - eapply Eq_SumFst; eauto 1.  
    specialize (H _ _ _ _ ltac:(eauto) _ ltac:(eauto));
    simpl in H; eauto.
  - eapply Eq_SumSnd; eauto 1.  
    specialize (H _ _ _ _ ltac:(eauto) _ ltac:(eauto));
    simpl in H; eauto.
  - simpl.
    eapply Eq_Case; eauto.
  - repeat rewrite subst_open; eauto 2 using CGrade_lc.
    pick fresh y and apply Eq_SubstIrrel; eauto 2. 
    eauto using subst_lc, CGrade_lc.    
    eauto using subst_lc, CGrade_lc.    
    repeat spec y.
    specialize (H2 P1 ([(y, psi)] ++ P2) x psi0).
    simpl_env in H2. specialize (H2 ltac:(auto)).
    specialize (H2 _ ltac:(eassumption)).
    repeat rewrite subst_open in H2; eauto 2 using CGrade_lc.
    rewrite subst_var_neq in H2. auto.
    auto.
  - eapply CDefEq_Nleq; eauto using subst_lc, CGrade_lc.
Qed.

Lemma DefEq_substitution_CGrade : 
  (forall P phi b1 b2, DefEq P phi b1 b2 -> forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a, CGrade P1 phi psi a
       -> DefEq (P2 ++ P1) phi (subst a x b1) (subst a x b2)). 
Proof.
  intros. 
  eapply CDefEq_DefEq_substitution_CGrade; eauto.
Qed.

Lemma DefEq_substitution_same : 
  (forall P phi b1 b2, DefEq P phi b1 b2 -> forall P1 P2 x psi, 
        P = P2 ++ [(x,psi)] ++ P1 
       -> forall a, Grade P1 phi a
       -> DefEq (P2 ++ P1) phi (subst a x b1) (subst a x b2)). 
Proof. 
  intros.
  eapply DefEq_substitution_CGrade; eauto.
Qed.

Lemma DefEq_substitution_irrel : forall (P : econtext) (psi : grade) (b1 b2 : tm),
       DefEq P psi b1 b2 ->
       forall (P1 P2 : list (atom * grade)) (x : atom) (phi : grade),
       P = P2 ++ [(x, phi)] ++ P1 ->
       not (phi <= psi) ->
       forall a : tm, lc a -> DefEq (P2 ++ P1) psi (subst a x b1) (subst a x b2).
Proof. 
  intros.
  eapply DefEq_substitution_CGrade; eauto.
  subst. apply DefEq_uniq in H. destruct_uniq.
  auto.
Qed.


Lemma DefEq_renaming : forall y x psi0 P psi b1 b2, 
    x `notin` dom P \u fv b1 \u fv b2 -> 
    y `notin` dom P \u fv b1 \u fv b2 \u {{x}} -> 
    DefEq ([(y, psi0)] ++ P) psi (open b1 (a_Var_f y)) (open b2 (a_Var_f y)) -> 
    DefEq ([(x, psi0)] ++ P) psi (open b1 (a_Var_f x)) (open b2 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_intro y b1); auto.
  rewrite (subst_intro y b2); auto.
  move: (DefEq_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply DefEq_substitution_same with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env. 2: eauto.
    eapply DefEq_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply DefEq_substitution_irrel  with (P2 := nil) (P1 := ([(x, psi0)] ++ P)); simpl_env.
    2: eauto.
    eapply DefEq_weakening_middle; eauto. 
    rewrite LE. done.
    eauto with lc.
Qed. 

Ltac exists_apply_DefEq x :=
  let y := fresh in
  fresh_apply_DefEq y; eauto;
  eapply (@DefEq_renaming x); try rewrite fv_close; auto;
  rewrite open_close; auto.


(* --- par ---- *)


Local Ltac par_subst2_ih :=
    match goal with 
      | [H3 : forall P3 x0 phi0 P4,
            (?y ~ ?psi0) ++ ?P2 ++ (?x ~ ?phi) ++?P1 = P3 ++ (x0 ~ phi0) ++ P4 -> _ |- _ ] => 
    specialize (H3 ([(y, psi0)] ++ P2) x phi P1 ltac:(reflexivity) _ ltac:(eassumption));
    simpl_env in H3;
    repeat rewrite subst_open in H3; eauto 3 using CGrade_lc, Par_lc1, Par_lc2;
    repeat rewrite subst_var_neq in H3 
    end.

Lemma CPar_Par_substitution_CGrade : (forall P psi psi0 a a', 
  CPar P psi psi0 a a' -> forall P2 x phi P1, P = (P2 ++ [(x, phi)] ++ P1) ->
  forall b, CGrade P1 psi phi b ->
  CPar (P2 ++ P1) psi psi0 (subst b x a) (subst b x a')) /\ (forall P psi a a', 
  Par P psi a a' -> forall P2 x phi P1, P = (P2 ++ [(x, phi)] ++ P1) ->
  forall b, CGrade P1 psi phi b ->
  Par (P2 ++ P1) psi (subst b x a) (subst b x a')).
Proof.
  apply CPar_Par_mutual.
  all: intros; subst.
  all: simp_syntax; eauto using Grade_substitution_CGrade, GEq_substitution_same, GEq_substitution_irrel.
  (* 9 subgoals *)
  all: repeat rewrite subst_open; eauto using CGrade_lc.
  all: try solve [econstructor; eauto; eapply H; eauto].
  all: try solve [fresh_apply_Par y; eauto; repeat spec y; try (eapply H; eauto);
                  par_subst2_ih; eauto].
  eapply CPar_Nleq; eauto using CGrade_lc, subst_lc.
Qed.

Lemma Par_substitution_CGrade : forall P2 x phi P1 psi a a', 
  Par (P2 ++ [(x, phi)] ++ P1) psi a a' -> 
  forall b, CGrade P1 psi phi b ->
  Par (P2 ++ P1) psi (subst b x a) (subst b x a').
Proof. intros. eapply CPar_Par_substitution_CGrade; eauto. Qed.

Lemma subst2 : forall x phi P1 psi a a' b, 
  Par ([(x, phi)] ++ P1) psi a a' -> 
  Grade P1 psi b ->
  Par P1 psi (subst b x a) (subst b x a').
Proof. intros. eapply Par_substitution_CGrade with (P2:=nil); eauto. Qed.

Lemma subst2_irrel : forall x phi P1 psi a a', 
  Par ([(x, phi)] ++ P1) psi a a' -> 
  forall b, not (phi <= psi) ->
  lc b ->
  Par P1 psi (subst b x a) (subst b x a').
Proof.
  intros.
  eapply Par_substitution_CGrade with (P2:=nil); eauto. 
  apply Par_uniq in H. destruct_uniq.
  eapply CG_Nleq; eauto.
Qed.

Lemma Par_renaming : forall y x psi0 P psi b1 b2, 
    x `notin` dom P \u fv b1 \u fv b2 -> 
    y `notin` dom P \u fv b1 \u fv b2 \u {{x}} -> 
    Par ([(y, psi0)] ++ P) psi (open b1 (a_Var_f y)) (open b2 (a_Var_f y)) -> 
    Par ([(x, psi0)] ++ P) psi (open b1 (a_Var_f x)) (open b2 (a_Var_f x)).
Proof.
  intros.
  rewrite (subst_intro y b1); auto.
  rewrite (subst_intro y b2); auto.
  move: (Par_uniq H1) => u. 
  destruct (q_leb psi0 psi) eqn:LE.
  - eapply subst2; eauto.
    eapply Par_weakening_middle; eauto. 
    eapply G_Var; eauto.
    solve_uniq.
  - eapply subst2_irrel; eauto with lc.
    eapply Par_weakening_middle; eauto. 
    rewrite LE. done.
Qed. 

Ltac exists_apply_Par x :=
  let y := fresh in
  fresh_apply_Par y; eauto;
  eapply (@Par_renaming x); try rewrite fv_close; auto;
  rewrite open_close; auto.

(* Par / CPar substitution *)

Lemma subst5_full :
 (forall P psi psi0 a a',
  CEq P psi psi0 a a' ->  forall P1 P2 x phi,
        P = P2 ++ [(x,phi)] ++ P1 
       -> forall b b', CPar P1 psi phi b b' 
       -> CPar (P2 ++ P1) psi psi0 (subst b x a) (subst b' x a')) /\
  (forall P psi a a',
  GEq P psi a a' -> forall P1 P2 x phi, 
        P = P2 ++ [(x,phi)] ++ P1 
       -> forall b b', CPar P1 psi phi b b' 
       -> Par (P2 ++ P1) psi (subst b x a) (subst b' x a')).
Proof.
  eapply CEq_GEq_mutual.
  all: intros; subst; simpl; eauto.  

  destruct (x == x0); subst;
  [  inversion H0; subst; eapply Par_weakening; eauto;
    apply binds_mid_eq in b; auto; subst; done
  | eauto].

  all: try move: (CEq_uniq c) => U; destruct_uniq.

  all : try solve [
  fresh_apply_Par y; eauto 3; repeat spec y;
  match goal with 
      | [H3 : forall P3 P4 x0 phi0,
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 = P4 ++ [(x0, phi0)] ++ P3 -> _ |- _ ] => 
    specialize (H3 P1 ([(y, psi0)] ++ P2) x phi ltac:(reflexivity) _ _ ltac:(eassumption));
    simpl_env in H3;
    repeat rewrite subst_open in H3; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2;
    repeat rewrite subst_var_neq in H3 end; eauto 3 ].
  eapply CPar_Nleq; eauto 3 using CPar_lc1, CPar_lc2, subst_lc.
Qed.


Lemma Par_subst3_full : forall P1 psi phi b b',
    CPar P1 psi phi b b' ->
    ((forall P psi1 psi0 a a', CPar P psi1 psi0 a a' -> forall P2 x, P = (P2 ++ [(x,phi)] ++ P1) -> psi = psi1 -> 
    CPar (P2 ++ P1) psi1 psi0 (subst b x a) (subst b' x a'))) /\ 
    (forall P psi1 a a', Par P psi1 a a' -> forall P2 x, P = (P2 ++ [(x,phi)] ++ P1) -> psi = psi1 ->
    Par (P2 ++ P1) psi1 (subst b x a) (subst b' x a')).
Proof.
  intros.
  apply CPar_Par_mutual.
  all: intros; subst; simp_syntax; eauto 4.
  (* refl case *)
  move: (subst5_full) => [_ h]. 
  eapply h; eauto using GEq_refl.

  all: repeat rewrite subst_open; eauto 2 using  CPar_lc1, CPar_lc2.
  all: eauto.
  all: try solve [  econstructor; eauto; eapply H0; eauto ].
  all: try solve [
  fresh_apply_Par y; try eapply H0; eauto 3; repeat spec y;
  match goal with 
      | [H3 : forall P3 x0,
            [(?y, ?psi0)] ++ ?P2 ++ [(?x, ?phi)] ++ ?P1 = P3 ++ [(x0, ?phi0)] ++ ?P5 -> _ |- _ ] => 
    specialize (H3 ([(y, psi0)] ++ P2) x ltac:(reflexivity) ltac:(reflexivity));
    simpl_env in H3;
    repeat rewrite subst_open in H3; eauto 3 using Grade_lc, CPar_lc1, CPar_lc2;
    repeat rewrite subst_var_neq in H3 end; eauto 3].
  destruct_uniq.
  eapply CPar_Nleq; eauto 3 using CPar_lc1, CPar_lc2, subst_lc.
Qed.

Lemma Par_subst3 : forall P1 phi b psi b' x,
    CPar P1 psi phi b b' ->
    forall a a', Par ([(x,phi)] ++ P1) psi a a' ->
    Par P1 psi (subst b x a) (subst b' x a').
Proof.
  intros.
  eapply Par_subst3_full with (P2 := nil); eauto.
Qed.

(* --------------------------- *)
