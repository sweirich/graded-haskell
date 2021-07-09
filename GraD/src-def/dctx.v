Require Import ssreflect.
Require Import Coq.Classes.EquivDec.
Require Import Metalib.Metatheory.
Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.

Require Import Qtt.usage.
Require Export Qtt.metalib.

Hint Rewrite dom_map : rewr_list.

(* ------------------------------------------------------------------- *)

(* An inversion tactic for ctx assumptions *)
Ltac invert_ctx := 
  repeat match goal with 
  | [ H : ctx nil ?G |- _ ] => inversion H; subst; clear H
  | [ H : ctx ?G nil |- _ ] => inversion H; subst; clear H
  | [ H : ctx (?a :: ?b) ?G |- _ ] => inversion H; subst; clear H
  | [ H : ctx ?D (?a :: ?b) |- _ ] => inversion H; subst; clear H
  | [ H : ctx ([?a] ++ ?b) ?G |- _ ] => inversion H; subst; clear H
  | [ H : ctx ?D ([?a] ++ ?b) |- _ ] => inversion H; subst; clear H
  | [ H : ctx [?a] ?G |- _ ] => inversion H; subst; clear H
  | [ H : ctx ?D [?G] |- _ ] => inversion H; subst; clear H
  end.


(* ------------------------------------------------------------------- *)
(*    Tactics and Structural Lemmas about the ctx judgement            *)
(* ------------------------------------------------------------------- *)

Lemma ctx_dom : forall {A}{D : list (atom * A)} {G}, ctx D G -> dom D = dom G.
induction 1; simpl; auto. f_equal; auto.
Qed.

Lemma ctx_uniq1 : forall {A}{D:list (atom * A)} {G}, ctx D G -> uniq D.
induction 1; auto.
Qed.

Lemma ctx_uniq2 : forall {A}{D:list (atom * A)} {G}, ctx D G -> uniq G.
induction 1; auto.
econstructor; auto. erewrite <- ctx_dom; auto.
Qed.

(* ------------------------------------------------------------------- *)


(* If we have identified a variable in the middle of a uniq environment, 
   it fixes the front and back. *)
Lemma ctx_mid {A} x (a a':(usage * A)) G1 : forall D G2 G1' G2',
    ctx D (G1 ++ (x ~ a) ++ G2) -> 
    (G1 ++ x ~ a ++ G2) = (G1' ++ x ~ a' ++ G2') ->
    G1 = G1' /\ a = a' /\ G2 = G2'.
Proof.   
  intros.
  move : (ctx_uniq2 H) => h1.
  eapply uniq_mid; eauto.
Qed.

Lemma ctx_mid2 {A} x (a a': A) : forall D1 D2 D1' D2' G,
    ctx (D1 ++ x ~ a ++ D2) G -> 
    (D1 ++ x ~ a ++ D2) = (D1' ++ x ~ a' ++ D2') ->
    D1 = D1' /\ a = a' /\ D2 = D2'.
Proof.   
  intros.
  move : (ctx_uniq1 H) => h1.
  eapply uniq_mid; eauto.
Qed.



(* Tactic to make applying this lemma easier. *)

Ltac ctx_mid := 
    let h  := fresh "VarCtx" in 
    let h1 := fresh "VarCtx" in 
    let h2 := fresh "VarCtx" in 
    let h3 := fresh "VarCtx" in 
    let h4 := fresh "VarCtx" in 
    let h5 := fresh "VarCtx" in 
    let h6 := fresh "VarCtx" in 
    let h7 := fresh "VarCtx" in 
    let h8 := fresh "VarCtx" in 
    match goal with 
      | [ H : ctx (?D1 ++ ?x ~ ?B ++ ?D2) (?G1 ++ ?x ~ (?q, ?A) ++ ?G2),
          Y : (?G1 ++ ?x ~ (?q, ?A) ++ ?G2) = ?G |- _ ] => 
        move: (ctx_uniq2 H) => h5;
        move: (uniq_mid _ _ _ _ _ _ _ _ h5 Y) => [h1 [h2 h3]];
        try match goal with 
        | [ H : (?a,?b) = (?c,?d) |- _ ] => inversion H; clear H
        end;
        subst
      end.



(* ------------------------------------------------------------------- *)


Lemma split_app : forall {A} {D1 : list (atom*A)}{G1 G1' D2 G2 G2'}, 
    ctx D1 G1 -> ctx D1 G1' -> 
    ctx D2 G1 -> ctx D2 G1' -> 
    G1 ++ G2 = G1' ++ G2'  -> G1 = G1' /\ G2 = G2'.
Proof.
      intros.
      move: D2 G1' H0 G2 G2' H1 H2 H3.
      dependent induction H.
      + intros. invert_ctx.  auto.
      + intros. invert_ctx.
        simpl_env in *.
        inversion H4. subst.
        edestruct IHctx; eauto. subst. auto.
Qed.


(* ------------------------------------------------------------------- *)

(* ctx operations preserve the ctx property *)


Lemma ctx_sub_ctx {A D}: forall{G1 G2 : list (atom * (usage * A))}, ctx_sub D G1 G2 -> ctx D G1 <-> ctx D G2.
Proof.
  induction D.
  intros. split; intro h; invert_ctx; inversion H; auto.
  intros. split; intro h; invert_ctx; inversion H; subst.
  econstructor; eauto. rewrite <- IHD; eauto.
  econstructor; eauto. rewrite IHD; eauto.
Qed. 

Lemma ctx_sub_ctx1 {A D}: forall{G1 G2 : list (atom * (usage * A))}, ctx_sub D G1 G2 -> ctx D G1.
Proof.
  induction D.
  all: intros; invert_ctx; inversion H; subst; econstructor.
  all: auto.
  all: eauto.
Qed.         

Lemma ctx_sub_ctx2 {A D}: forall{G1 G2 : list (atom * (usage * A))}, ctx_sub D G1 G2 -> ctx D G2.
Proof.
  induction D.
  all: intros; invert_ctx; inversion H; subst; econstructor.
  all: auto.
  all: eauto.
Qed.         


Lemma ctx_plus_ctx : forall {A}{D:list(atom*A)}{G1 G2} 
    (h1:ctx D G1) (h2: ctx D G2), ctx D (ctx_plus G1 G2).
Proof.
  induction D.
  - intros. invert_ctx. simpl.
    auto. 
  - intros. invert_ctx. simpl.
    econstructor; eauto.
Qed.

Lemma ctx_mul_ctx {A}{u}{D:list(atom*A)}{G} : ctx D G -> ctx D (ctx_mul u G).
Proof. 
  induction 1. simpl. auto. econstructor; eauto. 
Qed.

Lemma ctx_mul_ctx_inv {A}{u}{d:list(atom*A)} : forall {l},  ctx d (ctx_mul u l) -> ctx d l.
Proof. 
  induction d. intros; invert_ctx. destruct l; inversion H0. auto. 
  intros. destruct l; invert_ctx. destruct p. destruct p. simpl in H2. inversion H2. subst.
  econstructor; eauto.
Qed.

Lemma ctx_app_ctx {A}{d1:list(atom*A)}{l1 d2 l2} (x1 : ctx d1 l1) (x2: ctx d2 l2) 
  : disjoint d1 d2 -> ctx (d1 ++ d2) (l1 ++ l2).
Proof. 
  induction x1.
  simpl. auto.
  simpl_env. unfold disjoint in *. simpl. intro h.
  econstructor. eapply IHx1. fsetdec.
  rewrite dom_app. fsetdec. 
Qed.

Lemma ctx_split1 {A}{d1:list(atom*A)} : forall {l1 d2 l2},
     ctx (d1 ++ d2) (l1 ++ l2) -> ctx d1 l1 -> ctx d2 l2.
Proof. 
  induction d1; intros; simpl_env in *. 
  invert_ctx. simpl_env in *. auto.
  invert_ctx. eapply IHd1; eauto.
Qed.



Lemma ctx_split_l {A}{D2:list(atom*A)} : forall {D1} {G0},
  ctx (D2 ++ D1) G0 -> 
  exists G2 G1, G0 = G2 ++ G1 /\ ctx D1 G1 /\ ctx D2 G2 /\ disjoint D2 D1.
Proof.
  induction D2; simpl_env; intros.
  exists nil. exists G0. simpl_env; auto.
  simpl_env in H. invert_ctx.
  edestruct IHD2 as [G2 [G1 [h0 [h1 [h2 h3]]]]]; eauto.
  subst.
  exists (x ~ (q,a0) ++ G2).  exists G1.
  repeat split. auto. auto.
  solve_uniq.
Qed.

Lemma ctx_split_r {A}{G2} : forall {D:list(atom*A)} {G1},
  ctx D (G2 ++ G1) -> 
  exists D2 D1, D = D2 ++ D1 /\ ctx D1 G1 /\ ctx D2 G2 /\ disjoint D2 D1.
Proof.
  induction G2; simpl_env; intros.
  exists nil. exists D. simpl_env; auto.
  simpl_env in H. invert_ctx.
  edestruct IHG2 as [D2 [D1 [h0 [h1 [h2 h3]]]]]; eauto.
  subst.
  exists (x ~ a0 ++ D2).  exists D1.
  repeat split. auto. auto. solve_uniq.
Qed.

(* ------------------------------------------- *)

(* ------------------------------------------- *)


Lemma var_ctx : forall {a}{D1:list(atom*a)}{x A B D2 G1 q G2},
        ctx (D1 ++ x ~ B ++ D2) (G1 ++ x ~ (q, A) ++ G2) ->
        A = B /\ ctx D1 G1 /\ ctx D2 G2 /\ x `notin` dom (D1 ++ D2) /\ disjoint D1 D2.
Proof. 
  intros.
  have U1: uniq (D1 ++ x ~ B ++ D2). eapply ctx_uniq1; eauto.
  have U2: uniq (G1 ++ x ~ (q,A) ++ G2). eapply ctx_uniq2; eauto.
  move: (ctx_split_l H) => [Ga [Gb [h0 [h1 [h2a h2b]]]]].
  inversion h1. subst. clear h1.
  apply (uniq_mid _ _ _ _ _ _ _ _ U2) in h0.
  move: h0 => [h3 [h4 h5]]. inversion h4. subst. clear h4.
  destruct_uniq.
  repeat split; auto.
Qed.

Lemma ctx_app_ctx2 : forall {A}{D:list(atom*A)} G, 
    ctx D G -> forall D1 G1, ctx (D1 ++ D) (G1 ++ G) -> ctx D1 G1.
Proof.
  induction 1; intros. simpl_env in *. auto.
  move: (var_ctx H1) => [? [? [? [? ?]]]]. 
  eapply IHctx. 
  eapply ctx_app_ctx; eauto.
Qed.




Ltac split_ctx := 
    let G0 := fresh "G" in
    let G1 := fresh "G" in
    let D0 := fresh "D" in
    let D1 := fresh "D" in
    let h0 := fresh "H" in
    let h1 := fresh "H" in
    let h2 := fresh "H" in
    let h3 := fresh "H" in
    match goal with 
      | [ H : ctx (?D2 ++ ?D1) ?G |- _ ] =>
        move: (ctx_split_l H) => [G0 [G1 [h0 [h1 [h2 h3]]]]]; clear H; subst G
      | [ H : ctx ?D (?G1 ++ ?G2) |- _ ] =>
        move: (ctx_split_r H) => [D0 [D1 [h0 [h1 [h2 h3]]]]]; clear H; subst D
    end.

Ltac var_ctx := 
    let h  := fresh "VarCtx" in 
    let h1 := fresh "VarCtx" in 
    let h2 := fresh "VarCtx" in 
    let h3 := fresh "VarCtx" in 
    let h4 := fresh "VarCtx" in 
    match goal with 
      | [ H : ctx (?D1 ++ ?x ~ ?B ++ ?D2) (?G1 ++ ?x ~ (?q, ?A) ++ ?G2) |- _ ] => 
        move: (var_ctx H) => [h [h1 [h2 [h3 h4]]]];
        simpl_env in h3
      end;
    match goal with 
      | [ H : ?A = ?A |- _ ] => clear H
    end 
.



(* ------------------------------------------------------------------ *)


(* A hook for developments that use this library to add their own 
   tactics to the 'ctx' solvers *)

Ltac typing_ctx := idtac.

Ltac destruct_ctx := 
  repeat first [split_ctx | invert_ctx ]; destruct_uniq.

Ltac clarify_ctx := 
  repeat first [ assumption
               | apply ctx_nil
               | apply ctx_cons
               | apply ctx_app_ctx
               | apply ctx_mul_ctx 
               | apply ctx_plus_ctx
               | typing_ctx
  ];
  auto;
  try tauto.


Ltac solve_ctx :=
   intros; 
   destruct_ctx ;
   clarify_ctx  ; 
   try unfold disjoint in *;
   try fsetdec ;
   fail "Not solvable by [solve_ctx]".

Ltac eapply_ctx :=
    match goal with 
      | [ |- ctx ?D nil ] => eapply ctx_nil
      | [ |- ctx ?D ([?a]) ] => eapply ctx_cons
      | [ |- ctx ?D ([?a] ++ ?G2) ] => eapply ctx_cons
      | [ |- ctx ?D (?a :: ?G2) ] => eapply ctx_cons
      | [ |- ctx ?D (?G1 ++ ?G2) ] => eapply ctx_app_ctx
      | [ |- ctx ?D (ctx_mul ?q ?G) ] => eapply ctx_mul_ctx
      | [ |- ctx ?D (ctx_plus ?G1 ?G2) ] => eapply ctx_plus_ctx
      | [ H : ctx ?D (ctx_mul ?q ?G)  |- ctx ?D ?G ] => 
        eapply ctx_mul_ctx_inv; eassumption
    end.

Ltac eclarify_ctx :=
  repeat first [eassumption | eapply_ctx | typing_ctx ].

Ltac esolve_ctx :=
   intros; 
   destruct_ctx ;
   eclarify_ctx  ; 
   try unfold disjoint in *;
   try fsetdec ;
   fail "Not solvable by [solve_ctx]".





(* ------------------------------------------------------------------- *)
(*   Structural Lemmas about the ctx_plus and ctx_mul operations       *)
(* ------------------------------------------------------------------- *)

Section CtxStruct.

Variable A:Type.

(** *** ctx_plus *) 

Lemma ctx_plus_app {D} :
  forall {G1:list(atom*(usage*A))} {G2 D' G1' G2'}, 
    ctx D G1 -> ctx D G2 -> ctx D' G1' -> ctx D' G2' ->
    ctx_plus (G1 ++ G1') (G2 ++ G2') = ctx_plus G1 G2 ++ ctx_plus G1' G2'.
Proof.
  induction D; intros; invert_ctx; simpl_env. auto.
  simpl.
  f_equal.
  eauto.
Qed.

Lemma ctx_plus_app_l {D2 D1 G2} : forall {G}{G1:list(atom*(usage*A))}{G3}, 
    ctx D2 G2 -> ctx D1 G1 -> ctx (D2 ++ D1) G3 ->
    G = ctx_plus (G2 ++ G1) G3 -> 
    exists G6 G7, G = ctx_plus G2 G6 ++ ctx_plus G1 G7 
             /\ (G3 = G6 ++ G7) /\ (ctx D2 G6) /\ ctx D1 G7.
Proof.
  intros.
  destruct (ctx_split_l H1) as [G2' [G1' [h0 [h1 [h2 h3]]]]]. subst.
  exists G2'. exists G1'.  erewrite ctx_plus_app; try eauto.
Qed.

Lemma ctx_plus_app_r {D2 D1 G2} : forall {G}{G1:list(atom*(usage*A))}{G3}, 
    ctx D2 G2 -> ctx D1 G1 -> ctx (D2 ++ D1) G3 ->
  G = ctx_plus G3 (G2 ++ G1) -> 
  exists G6 G7, G = ctx_plus G6 G2 ++ ctx_plus G7 G1 
           /\ (G3 = G6 ++ G7) /\ (ctx D2 G6) /\ ctx D1 G7.
Proof.
  intros.
  destruct_ctx.
  erewrite ctx_plus_app in H2; try eauto.
  eexists. eexists.
  repeat split; eauto.
Qed.

Lemma ctx_plus_app_result {D2} : forall {G2:list(atom*(usage*A))}{D1 G G1 G3},
    ctx D2 G2 -> ctx D1 G1 ->
    ctx (D2 ++ D1) G -> ctx (D2 ++ D1) G3 ->
    G2 ++ G1 = ctx_plus G G3 ->
    exists G4 G5 G6 G7, 
      G = G4 ++ G5 /\ ctx D2 G4 /\ ctx D1 G5 /\
      G3 = G6 ++ G7 /\ ctx D2 G6 /\ ctx D1 G7 /\
      G2 = ctx_plus G4 G6 /\ G1 = ctx_plus G5 G7.
Proof.
  induction D2; intros; simpl_env in *.
  + invert_ctx; simpl_env in *. subst.
    exists nil. exists G. exists nil. exists G3.
    simpl_env. repeat split; auto.
  + invert_ctx. 
    simpl in H3. inversion H3. clear H3. 
    edestruct IHD2 as [G4 [G5 [G6 [G7 h]]]]. 
    5: try eassumption. all: try eassumption.
    move: h => [h0 [h1 [h2 [h3 [h4 [h5 [h6 h7]]]]]]].
    subst.
    eexists. eexists. eexists. eexists.
    split. rewrite <- app_assoc. reflexivity. 
    split. econstructor; auto.
    split. auto. 
    split. rewrite <- app_assoc. reflexivity.
    split. econstructor; auto. 
    split. auto. 
    split. simpl. auto.
    auto.
Qed.

Lemma ctx_plus_Irr (G:list(atom*(usage*A))) : G = ctx_plus G (ctx_mul 0 G).
Proof. induction G. simpl; auto.
      destruct a. destruct p. 
      simpl. rewrite qmul_0_l. rewrite qplus_0_r. f_equal.
      auto.
Qed.

(** ** ctx_mul *)

Lemma ctx_mul_app q (G1:list(atom*(usage*A))) G2 : ctx_mul q (G1 ++ G2) = ctx_mul q G1 ++ ctx_mul q G2.
Proof.
  unfold ctx_mul. rewrite map_app. auto.
Qed.


Lemma ctx_mul_app_inv : forall {q}{G1:list(atom*(usage*A))}{G2}, G1 ++ G2 = ctx_mul q G1 ++ ctx_mul q G2 -> G1 = ctx_mul q G1 /\ G2 = ctx_mul q G2.
Proof. 
   induction G1; intros; auto. 
   - destruct a; simpl in *; simpl_env in *.
     inversion H.
     specialize (IHG1 G2).
     move: (IHG1 H2) => [h1 h2].
     split;
       repeat f_equal; auto.
Qed.

Lemma ctx_mul_cons x q a q1 (G:list(atom*(usage*A))) : ctx_mul q (x ~ (q1,a) ++ G) = x ~ (q * q1,a) ++ ctx_mul q G.
Proof.
  unfold ctx_mul. auto.
Qed.

Lemma ctx_mul_nil q : @ctx_mul A q nil = nil.
Proof.
  unfold ctx_mul. auto.
Qed.

Lemma ctx_mul_app_r: forall q (G1:list(atom*(usage*A))) G G2, (ctx_mul q G = G1 ++ G2) ->
                      exists G1' G2', ctx_mul q G1' = G1 /\ ctx_mul q G2' = G2.
Proof.
 induction G1. intros. simpl in H. exists nil. exists G. simpl. subst. auto.
  intros. destruct G as [|[x [q1 a0]]]; inversion H. clear H. subst.
  move: (IHG1 _ _ H2) => [G1' [G2' [E1 E2 ]]].
  exists (x ~ (q1,a0) ++ G1'). exists G2'.
  simpl. split. f_equal. auto. auto.
Qed.


Lemma ctx_mul_app_split: forall q (G:list(atom*(usage*A))) G1 G2, ctx_mul q G = ctx_mul q G1 ++ ctx_mul q G2 ->
                             exists G1', exists G2', G = G1' ++ G2' 
                                           /\ ctx_mul q G1 = ctx_mul q G1'
                                           /\ ctx_mul q G2 = ctx_mul q G2'.
Proof. 
  induction G; intros.
  + exists nil. exists nil.
    destruct G1; destruct G2; simpl in H; inversion H.
    auto.
  + destruct a as [x [q1 ?]]. 
    destruct G1; simpl in H; inversion H.
    ++ (* G1 is nil *)
      destruct G2; simpl in H; inversion H;
        destruct p as [? [? ?]]; simpl in H2; inversion H2; subst; clear H2.
      specialize (IHG nil G2). rewrite H3 in IHG.
      move: (IHG ltac:(simpl; reflexivity)) => [G1' [G2' [? [h0 h1]]]]. subst.
      destruct G1'; simpl in h0; inversion h0.
      exists nil. exists  ((a0, (q1, a1)) :: G2'). simpl_env. split; auto.
    ++ (* G1 is not nil *)
      destruct p as [? [? ?]]; simpl in H1; inversion H1; subst. clear H1 H.
      specialize (IHG G1 G2 H2). 
      move: IHG => [G1' [G2' [? [h0 h1]]]].
      exists ((a0, (q1, a1))::G1'). exists G2'.
      subst.
      simpl_env. split. auto.
      split. repeat rewrite ctx_mul_app. 
      simpl. f_equal. rewrite H4. auto. auto. auto.
Qed.

(* -------------------------------------------------------- *)



End CtxStruct.

Hint Rewrite ctx_mul_app ctx_mul_cons ctx_mul_nil : rewr_list.
