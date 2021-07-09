Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels. 

Set Implicit Arguments.
Open Scope grade_scope.

(* Helps with specializing the IH for weakening proofs. *)
Local Ltac weakening_ih := 
    match goal with 
    | [ H3 : forall P4 P5, [(?x, ?psi0)] ++ ?P2 ++ ?P1 ~= P4 ++ P5 -> _ |- _ ]
     => specialize (H3 (x ~ psi0 ++ P2) P1 ltac:(auto) ltac:(simpl_env;auto)); simpl_env in H3
     end.

Lemma Grade_weakening_middle : forall P3 P2 P1 psi b,
    Grade (P2 ++ P1) psi b
    -> uniq (P2 ++ P3 ++ P1) 
    -> Grade (P2 ++ P3 ++ P1) psi b.     
Proof. 
  intros. 
  dependent induction H.
  all: eauto.
  all: try solve 
        [fresh_apply_Grade x; auto;
         repeat spec x;
         weakening_ih;
         eauto].
Qed.

Lemma Grade_weakening : forall P2 P1 psi b,
    Grade P1 psi b
    -> uniq (P2 ++ P1) 
    -> Grade (P2 ++ P1) psi b.     
Proof. 
  intros.
  eapply Grade_weakening_middle with (P2 := nil); simpl_env; eauto.
Qed.

Ltac geq_weakening_ih := 
    match goal with 
    | [ H3 : forall P3 P4, [(?x, ?psi0)] ++ ?P2 ++ ?P1 = P4 ++ P3 -> _ |- _ ]
     => specialize (H3 P1 ([(x,psi0)] ++ P2) ltac:(eauto) _ ltac:(simpl_env;eauto)); simpl_env in H3
     end.

Lemma CEq_GEq_weakening : 
  (forall P phi phi0 a b,
  CEq P phi phi0 a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> CEq (P2 ++ P3 ++ P1) phi phi0 a b) /\
  (forall P phi a b,
  GEq P phi a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> GEq (P2 ++ P3 ++ P1) phi a b).
Proof.
  eapply CEq_GEq_mutual.
  all: intros; eauto.
  all: try solve [subst; eapply GEq_Var; eauto].
  all: try solve [subst;
    fresh_apply_GEq x; eauto;
    repeat spec x;
    geq_weakening_ih;
    eauto].
Qed.

Lemma GEq_weakening_middle :  (forall P phi a b,
  GEq P phi a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> GEq (P2 ++ P3 ++ P1) phi a b).
Proof.
  destruct CEq_GEq_weakening.
  auto.
Qed.


Lemma GEq_weakening : forall P phi b1 b2,
  GEq P phi b1 b2 -> forall P2, uniq (P2 ++ P) -> GEq (P2 ++ P) phi b1 b2. 
Proof.
  destruct CEq_GEq_weakening.
  intros.
  eapply H0 with (P2 := nil); eauto.
Qed.

Lemma DefEq_weakening_middle : 
  (forall P phi a b,
  DefEq P phi a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> DefEq (P2 ++ P3 ++ P1) phi a b).
Proof.
  intros P Phi a b h. induction h.
  all: intros; subst; eauto 3 using Grade_weakening_middle.
  all: try solve [subst;
    fresh_apply_DefEq x; auto;
    repeat spec x;
    geq_weakening_ih;
    eauto].
  all: try solve [
             pick fresh x and apply Eq_SubstIrrel; eauto 2;
             repeat spec x;
             geq_weakening_ih;
             eauto].

  all: eauto 4 using Grade_weakening_middle.
  all: try (eapply Eq_Case; eauto 3 using Grade_weakening_middle).
Qed.

Lemma DefEq_weakening : forall P phi b1 b2,
  DefEq P phi b1 b2 -> forall P2, uniq (P2 ++ P) -> DefEq (P2 ++ P) phi b1 b2. 
Proof.
  intros.
  eapply DefEq_weakening_middle with (P2 := nil); eauto.
Qed.

Lemma Par_weakening_middle :
  forall G0 a psi b, Par G0 psi a b ->
  forall E F G, (G0 = F ++ G) -> uniq (F ++ E ++ G) ->  Par (F ++ E ++ G) psi a b.
Proof.
  intros P Phi a b h. induction h.
  all: intros; subst; eauto 3 using Grade_weakening_middle.
  all: try solve [
  subst; fresh_apply_Par x; auto; repeat spec x;
  match goal with 
  | [ H3 : forall E F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G = F0 ++ G0 -> _ |- _ ]
    =>  specialize (H3 E ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto) ltac:(simpl_env;eauto)) ;
  simpl_env in H3 end; eauto].

  all: eauto 5 using Grade_weakening_middle.
Qed.

Lemma Par_weakening :
  forall G a psi b, Par G psi a b ->
  forall E, uniq (E ++ G) ->  Par (E ++ G) psi a b.
Proof.
  intros. eapply Par_weakening_middle with (F := nil); eauto.
Qed.


Lemma Typing_weakening_middle : forall W2 W1 q b B, 
    Typing (W2 ++ W1) q b B ->
    forall W, uniq (W2 ++ W ++ W1) ->
    Typing (W2 ++ W ++ W1) q b B.
Proof.
  intros W2 W1 q b B h. dependent induction h.
  all: intros; subst; eauto 3 using DefEq_weakening_middle.
  all: have UL1: uniq (meet_ctx_l q_C W2 ++ meet_ctx_l q_C W ++ meet_ctx_l q_C W1) by
    unfold meet_ctx_l; solve_uniq.
  all: have UL2: uniq (labels (meet_ctx_l q_C W2) ++ labels (meet_ctx_l q_C W) ++ labels (meet_ctx_l q_C W1)) by
   unfold labels; solve_uniq.
  (* easy cases *)
  all: try solve [eapply T_App; eauto].
  all: try solve [
             eapply T_AppIrrel; simpl_env; eauto;
             eapply IHh2; simpl_env; eauto].
  all: try solve [
             apply T_WPair; simpl_env; eauto;
             eapply IHh1; simpl_env; eauto].
  all: try solve [
             apply T_WPairIrrel; simpl_env; eauto;
             try eapply IHh1; simpl_env; eauto;
             try eapply IHh2; simpl_env; eauto].
  all: try solve [
             apply T_SPair; simpl_env; eauto;
             try eapply IHh1; simpl_env; eauto;
             try eapply IHh2; simpl_env; eauto].
  all: try solve [
             apply T_Sum; simpl_env; eauto;
             try eapply IHh1; simpl_env; eauto;
             try eapply IHh2; simpl_env; eauto].
  all: try solve [
             eapply T_Inj1; simpl_env; eauto;
             eapply IHh2; simpl_env; eauto].
  all: try solve [
             eapply T_Inj2; simpl_env; eauto;
             eapply IHh2; simpl_env; eauto].
  all: try solve [eapply T_Eq; simpl_env; eauto].
  
  (* conversion *)
  all: try match goal with [ H : DefEq _ _ _ _ |- _ ] => 
                  eapply T_Conv; eauto 3;
                    simpl_env in *;
                    try eapply DefEq_weakening_middle; eauto end.

  (* pi *)
  subst; fresh_apply_Typing x; auto; repeat spec x;
  match goal with 
  | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G ~= F0 ++ G0 -> _ |- _ ]
    => specialize (H3 ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto 3)) ;
  simpl_env in H3; eauto 3; try eapply H3; try solve_uniq end.

  (* abs *)
  subst; fresh_apply_Typing x; simpl_env; try eapply IHh; simpl_env; eauto; repeat spec x;
  try match goal with 
  | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G ~= F0 ++ G0 -> _ |- _ ]
    => specialize (H3 ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto 3) W) ;
  simpl_env in H3 ; eauto 3; try eapply H3 end. 

  (* wsigma *)
  subst; fresh_apply_Typing x; auto; repeat spec x;
  match goal with 
  | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G ~= F0 ++ G0 -> _ |- _ ]
    => specialize (H3 ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto 3)) ;
  simpl_env in H3; eauto 3; try eapply H3; try solve_uniq end.

  (* letpair *)
  - subst; fresh_apply_Typing x. 
    + clear H H1 H2 IHh.
    repeat spec x. simpl_env.
    match goal with 
    | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ meet_ctx_l q_C (?F ++ ?G) ~= F0 ++ G0 -> _ |- _ ]
      => specialize (H3 ([(x,psi0)] ++ meet_ctx_l q_C F) (meet_ctx_l q_C G) ltac:(simpl_env;eauto 3) (meet_ctx_l q_C W));
          simpl_env in H3; eapply H3 end.
    eapply uniq_cons_3; auto. repeat rewrite dom_app. repeat rewrite dom_meet_ctx_l. auto.
    + eapply IHh; auto.
    + move => y Fry.
      clear H H0 H1 IHh.
      spec x. spec y.
      specialize (H0 ([(x, (psi0 * psi,A))] ++ W2) W1 ltac:(simpl_env; auto) W).
      simpl_env in H0. eapply H0. solve_uniq.

  (* ssigma *)
  - subst; fresh_apply_Typing x; auto; repeat spec x;
      match goal with 
      | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G ~= F0 ++ G0 -> _ |- _ ]
        => specialize (H3 ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto 3)) ;
            simpl_env in H3; eauto 3; try eapply H3; try solve_uniq end.
  - (* case *)
    fresh_apply_Typing x; auto.
    repeat spec x.
    simpl_env.
    match goal with 
    | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ meet_ctx_l q_C (?F ++ ?G) ~= F0 ++ G0 -> _ |- _ ]
      => specialize (H3 ([(x,psi0)] ++ meet_ctx_l q_C F) (meet_ctx_l q_C G) ltac:(simpl_env;eauto 3)
                   (meet_ctx_l q_C W));
          simpl_env in H3 ; eapply H3 end.
    eapply uniq_cons_3; auto. repeat rewrite dom_app. repeat rewrite dom_meet_ctx_l. auto.
Qed.    

Lemma Typing_weakening : forall W1 q b B, 
    Typing W1 q b B ->
    forall W2, uniq (W2 ++ W1) -> 
    Typing (W2 ++ W1) q b B.
Proof. 
  intros.
  eapply Typing_weakening_middle with (W2 := nil); simpl_env; eauto.
Qed.
