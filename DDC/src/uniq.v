Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels. 

Set Implicit Arguments.
Open Scope grade_scope.

Lemma P_sub_uniq1 : forall P P', P_sub P P' -> uniq P.
Proof. intros. induction H; eauto. Qed.

Lemma P_sub_uniq2 : forall P P', P_sub P P' -> uniq P'.
Proof. intros. induction H; eauto. Qed.

Lemma ctx_sub_uniq : forall (W1 W2 : context), ctx_sub W2 W1 -> uniq W1 -> uniq W2.
Proof.
  induction 1; intros; eauto.
  destruct_uniq.
  specialize (IHctx_sub ltac:(auto)).
  solve_uniq.
Qed.

Arguments ctx_sub_uniq {_} {_}.


Lemma Grade_uniq : forall P psi a, Grade P psi a -> uniq P.
Proof. intros; induction H; eauto. 
       pick fresh x; repeat spec x.
       match goal with [ H2 : uniq ([_] ++ _) |- _ ] => inversion H2; auto end.
Qed.

Lemma CEq_GEq_uniq : 
  (forall P phi phi0 a b,
  CEq P phi phi0 a b -> uniq P) /\
  (forall P phi a b,
  GEq P phi a b -> uniq P).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; eauto.
  all: try (pick fresh x; spec x; solve_uniq).
  (* eauto using Grade_uniq. *)
Qed.

Lemma CEq_uniq : forall P phi phi0 a b,
  CEq P phi phi0 a b -> uniq P.
Proof. eapply CEq_GEq_uniq. Qed.
Lemma GEq_uniq :
  (forall P phi a b,
  GEq P phi a b -> uniq P).
Proof. eapply CEq_GEq_uniq. Qed.

Lemma DefEq_uniq : (forall P phi a b,
  DefEq P phi a b -> uniq P).
Proof. 
  induction 1.
  all: intros; eauto 3 using Grade_uniq.
  all: try pick fresh x; spec x; solve_uniq.
Qed.

Lemma Par_uniq : forall P psi a b, Par P psi a b -> uniq P.
Proof. intros. induction H; eauto. eapply Grade_uniq; eauto. 
pick fresh x; spec x; solve_uniq. Qed.

Lemma MultiPar_uniq : forall P psi a b, MultiPar P psi a b -> uniq P.
Proof. induction 1; eauto using Grade_uniq. Qed.

Lemma Typing_uniq : forall W psi a A, Typing W psi a A -> uniq W.
Proof. induction 1; unfold join_ctx_l in *; eauto using uniq_map_1. Qed.
