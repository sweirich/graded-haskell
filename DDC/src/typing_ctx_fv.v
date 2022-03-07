Require Export Qual.grade. 
Require Export Qual.defeq.
Require Export Qual.labels.

Set Implicit Arguments.
Open Scope grade_scope.


Definition Ctx_Prop (W:context) := (forall x psi A, binds x (psi, A) W -> fv A [<=] dom W).

Lemma Ctx_Prop_meet_ctx_l : forall W, Ctx_Prop W -> Ctx_Prop (meet_ctx_l q_C W).
Proof. intros W. unfold Ctx_Prop. intros.
       unfold meet_ctx_l in H0. 
       apply binds_map_3 in H0. destruct H0 as [[g B] hh]. split_hyp.
       rewrite -> dom_meet_ctx_l in *. invert_equality. eapply H. eauto.
Qed.       

Lemma Ctx_Prop_cons : forall x q A W, fv A [<=] dom W -> Ctx_Prop W -> Ctx_Prop ([(x, (q, A))] ++ W).
Proof.
  intros.
  unfold Ctx_Prop in *.
  intros.
  eapply binds_cons_1 in H1. destruct H1. split_hyp. invert_equality.
  simpl. rewrite H. fsetdec.
  simpl. rewrite H0. fsetdec. eauto.
Qed.

#[global] Opaque Syntax_tm. 
#[global] Opaque Subst_tm.
#[global] Opaque SubstOpen_tm.


Lemma Typing_ctx_fv_helper : forall W psi a A, Typing W psi a A -> Ctx_Prop W -> fv a [<=] dom W /\ fv A [<=] dom W.
Proof.
  intros W psi a A H CTX. induction H.

  all: split; simp_syntax. 

  all: try rewrite -> dom_meet_ctx_l in *. 

  all: repeat match goal with [ H : Ctx_Prop _ -> _ |- _ ] => specialize (H ltac:(eauto using Ctx_Prop_meet_ctx_l)) end.
  all: split_hyp.
  all: try (move: (binds_In _ _ _ _ H1) => h; fsetdec). 
  all: try solve [ unfold Ctx_Prop in CTX; eauto ].


  all: try rewrite -> dom_meet_ctx_l in H1. 
  all: try rewrite -> dom_meet_ctx_l in H2. 
  all: try rewrite -> dom_meet_ctx_l in H3.
  all: try rewrite -> dom_meet_ctx_l in H4.
  all: try rewrite -> dom_meet_ctx_l in H5.
  all: try rewrite -> dom_meet_ctx_l in H6.
  all: try rewrite -> dom_meet_ctx_l in H7.

  all: try fsetdec.

  all: try solve [rewrite fv_open_upper;
                  fsetdec].

  all: try solve [try rewrite <- fv_open_lower in *;
                  fsetdec].

  all: pick fresh z. 
  all: repeat spec z.
  all: pick fresh w.
  all: repeat spec w.
  all: move: (Ctx_Prop_meet_ctx_l CTX) => MCTX.
  all: try match goal with [H : Ctx_Prop ?C -> fv (open _ _) [<=] _ /\ _ |- _ ] => 
                            rewrite <- fv_open_lower in H end. 
  all:  have lemma: forall x A B, A [<=] add x B -> x `notin` A ->  A [<=] B by clear; intros; fsetdec.


Admitted.

(* need more fv rewrites 

  - match goal with [ H4 : Ctx_Prop _ -> _ |- _ ] =>  specialize (H4 ltac:(eapply Ctx_Prop_cons; auto; try fsetdec)) end.
    split_hyp.
    move: (lemma z _ _ H0 ltac:(fsetdec)) => h.
    eapply AtomSetProperties.union_subset_3; auto.

  - admit. 
    (* match goal with [ H4 : Ctx_Prop _ -> _ |- _ ] =>  specialize (H4 ltac:(eapply Ctx_Prop_cons; auto; try fsetdec)) end.
    split_hyp.
    move: (lemma z _ _ H ltac:(fsetdec)) => h.
    eapply AtomSetProperties.union_subset_3; auto.
    fsetdec. *)


  - match goal with [ H4 : Ctx_Prop _ -> _ |- _ ] =>  specialize (H4 ltac:(eapply Ctx_Prop_cons; auto; try fsetdec)) end.
    split_hyp.
    move: (lemma z _ _ H0 ltac:(fsetdec)) => h.
    eapply AtomSetProperties.union_subset_3; auto.

  - specialize (H3 ltac:(eapply Ctx_Prop_cons; auto; try fsetdec)).
    split_hyp.
    move: (lemma z _ _ H3 ltac:(fsetdec)) => h.
    eapply AtomSetProperties.union_subset_3; auto.

  - destruct H2.
    eapply Ctx_Prop_cons; auto. simpl. rewrite dom_meet_ctx_l. auto.
    rewrite fv_open_upper.
    rewrite <- fv_open_lower in H2.
    rewrite dom_meet_ctx_l in H2.
    have FC: z `notin` fv C.  clear Fr0. auto.
    move: (lemma z _ _ H2 FC) => h.
    clear Fr Fr0. fsetdec.

  - destruct H5.
    eapply Ctx_Prop_cons; auto. simpl. 
    move: (lemma z _ _ H0 ltac:(fsetdec)) => h.
    eapply AtomSetProperties.union_subset_3; auto.

  - destruct H2.
    clear Fr0.
    eapply Ctx_Prop_cons; auto. simpl. rewrite dom_meet_ctx_l. auto.
    rewrite -> dom_meet_ctx_l in H.
    rewrite fv_open_upper.
    have FC: z `notin` fv B.  clear Fr0. auto.
    move: (lemma z _ _ H FC) => h.
    eapply AtomSetProperties.union_subset_3; auto.

Qed.     *)

Lemma Typing_ctx_fv_Ctx : forall W, Ctx W -> Ctx_Prop W.
induction 1. unfold Ctx_Prop. intros. inversion H.
eapply Ctx_Prop_cons.
move: (Typing_ctx_fv_helper H0 (Ctx_Prop_meet_ctx_l IHCtx)) => ih.
split_hyp.
rewrite dom_meet_ctx_l in H2. auto. auto.
Qed.
  
Lemma Typing_ctx_fv : forall W psi a A, Typing W psi a A -> Ctx W -> fv a [<=] dom W /\ fv A [<=] dom W.
Proof.
  intros.
  eapply Typing_ctx_fv_helper; eauto.
  eapply Typing_ctx_fv_Ctx; eauto.
Qed.
