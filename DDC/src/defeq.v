Require Export Qual.metalib.
Require Export Qual.grade. 
Require Export Qual.geq.

Set Implicit Arguments.
Open Scope grade_scope.


Lemma CDefEq_DefEq_Grade : 
  (forall P psi phi a b, CDefEq P psi phi a b -> CGrade P psi phi a /\ CGrade P psi phi b) /\
  (forall P psi a b, DefEq P psi a b -> Grade P psi a /\ Grade P psi b).
Proof.
  apply CDefEq_DefEq_mutual.
  all: intros; split; split_hyp; eauto.
  all: try solve [eauto using leq_join_r ].
  all: try solve [repeat invert_Grade; subst; eauto].
  all: try solve [fresh_apply_Grade x; auto;
    repeat spec x; split_hyp; eauto].
  all: try solve [repeat invert_Grade; subst;
    pick fresh x; repeat spec x;
    eapply Grade_open; eauto using leq_join_r].

  all: pick fresh x;
  repeat spec x;
  split_hyp.
  inversion H0; subst.
  eapply Grade_open with (y := x); eauto.
  eapply Grade_open_irrel with (y := x); eauto.
  inversion H1; subst.
  eapply Grade_open with (y := x); eauto.
  eapply Grade_open_irrel with (y := x); eauto.
Qed.

Lemma DefEq_Grade : forall P psi a b, DefEq P psi a b -> Grade P psi a /\ Grade P psi b.
Proof. apply  CDefEq_DefEq_Grade. Qed.

Lemma DefEq_Grade1 : forall {W psi a b}, DefEq W psi a b -> Grade W psi a. 
eapply DefEq_Grade; auto. Qed.
Lemma DefEq_Grade2 : forall {W psi a b}, DefEq W psi a b -> Grade W psi b. 
eapply DefEq_Grade; auto. Qed.


Lemma CEqGEq_DefEq : 
  (forall P phi phi0 a b, CEq P phi phi0 a b -> CDefEq P phi phi0 a b) /\
  (forall P phi a b, GEq P phi a b -> DefEq P phi a b).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; eauto 3.
Qed.


Lemma CDefEq_substitution1 : forall P2 x psi0 P1 psi a a1 a2, 
  Grade (P2 ++ [(x, psi0)] ++ P1) psi a -> 
  CDefEq P1 psi psi0 a1 a2 -> 
  Grade (P2 ++ P1) psi (subst_tm_tm a1 x a).
Proof. 
  intros.
  inversion H0; subst.
  eapply Grade_substitution_same; eauto using DefEq_Grade1.
  eapply Grade_substitution_irrel; eauto using DefEq_lc1.
Qed.

Lemma CDefEq_substitution2 : forall P2 x psi0 P1 psi a a1 a2, 
  Grade (P2 ++ [(x, psi0)] ++ P1) psi a -> 
  CDefEq P1 psi psi0 a1 a2 -> 
  Grade (P2 ++ P1) psi (subst_tm_tm a2 x a).
Proof. 
  intros.
  inversion H0; subst.
  eapply Grade_substitution_same; eauto using DefEq_Grade2.
  eapply Grade_substitution_irrel; eauto using DefEq_lc2.
Qed.

Parameter star : sort.

Lemma DefEq_equality_substitution : (forall P phi b1 b2,
  DefEq P phi b1 b2 -> forall P1 x psi, 
        P = [(x,psi)] ++ P1 
       -> forall a1 a2, DefEq P1 phi a1 a2  
       -> psi <= phi
       -> DefEq P1 phi (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2)). 
Proof. 
  intros. subst.
  move: (DefEq_uniq H) => u. destruct_uniq.
  repeat rewrite subst_tm_tm_spec.
  pick fresh y and apply Eq_Subst; eauto 2.
  eapply (@DefEq_renaming x). 
  repeat rewrite fv_tm_tm_close_tm_wrt_tm. fsetdec.
  repeat rewrite fv_tm_tm_close_tm_wrt_tm. fsetdec.
  rewrite open_tm_wrt_tm_close_tm_wrt_tm.
  rewrite open_tm_wrt_tm_close_tm_wrt_tm.
  auto.
Qed.

Lemma DefEq_substitution_irrel2 : (forall P phi b1 b2,
  DefEq P phi b1 b2 -> forall P1 x psi, 
        P = [(x,psi)] ++ P1 
       -> not (psi <= phi)
       -> forall a1 a2, lc_tm a1 -> lc_tm a2
       -> DefEq P1 phi (subst_tm_tm a1 x b1) (subst_tm_tm a2 x b2)). 
Proof.
  intros. subst.
  move: (DefEq_uniq H) => u. destruct_uniq.
  rewrite subst_tm_tm_spec.
  rewrite subst_tm_tm_spec.
  pick fresh y and apply Eq_Subst; eauto 2.
  eapply (@DefEq_renaming x). repeat rewrite fv_tm_tm_close_tm_wrt_tm. fsetdec.
  repeat rewrite fv_tm_tm_close_tm_wrt_tm. fsetdec.
  rewrite open_tm_wrt_tm_close_tm_wrt_tm.
  rewrite open_tm_wrt_tm_close_tm_wrt_tm.
  auto.
Qed.
