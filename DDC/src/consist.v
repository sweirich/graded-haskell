Require Import Omega.
Require Export Qual.geq.
Require Export Qual.defeq.
Require Export Qual.par.
Require Export Qual.confluence.

Set Implicit Arguments.

(* These lemmas talk about what MultiPar does for ValueTypes. Once Par has revealed the head form 
   of a type, it never changes. *)


Lemma MultiPar_Type_inv : forall S A psi B s, MultiPar S psi A B -> A = a_Type s -> B = a_Type s.
Proof.
  intros S A psi B s H. induction H. auto.
  inversion H; intro K; auto; try inversion K.
Qed.

Lemma MultiPar_TyUnit_inv : forall S A psi B, MultiPar S psi A B -> A = a_TyUnit -> B = a_TyUnit.
Proof.
  intros S A psi B H. induction H. auto.
  inversion H; intro K; auto; try inversion K.
Qed.


Lemma MultiPar_Pi_inv : forall S D rho A B, 
    MultiPar S D A B -> 
    forall A1 A2, A = a_Pi rho A1 A2 ->
             exists B1 B2, B = (a_Pi rho B1 B2) /\
                      MultiPar S D A1 B1 /\
                      exists L, forall x, x \notin L -> 
                                MultiPar ([(x,D)] ++ S) D (open_tm_wrt_tm A2 (a_Var_f x)) 
                                         (open_tm_wrt_tm B2 (a_Var_f x)).
Proof.
  intros S D rho A B H. 
  induction H; intros; subst; try invert_Grade; subst.
  + eexists. eexists. split; try reflexivity. repeat split; eauto.
  + inversion H; subst; 
    destruct (IHMultiPar _ _ ltac:(auto)) as [B01 [B02 EQ]]; 
    auto; split_hyp; subst.
    exists B01, B02; repeat split; auto.
    eapply MP_Step; eauto.
    move: H3 => [L0 h].
    exists (L \u L0). move=> x Fr. repeat spec x.
    eapply MP_Step; eauto.
Qed. 

Lemma MultiPar_WSigma_inv : forall S D rho A B, MultiPar S D A B -> forall A1 A2,
      A = a_WSigma rho A1 A2 ->
      exists B1 B2, B = (a_WSigma rho B1 B2)
               /\ MultiPar S D A1 B1 /\
               exists L, forall x, x \notin L -> 
                         MultiPar ([(x,D)] ++ S) D (open_tm_wrt_tm A2 (a_Var_f x)) 
                                  (open_tm_wrt_tm B2 (a_Var_f x)).
Proof.
  intros S D rho A B H. 
  induction H; intros; subst; try invert_Grade; subst.
  + eexists. eexists. split; try reflexivity. repeat split; eauto.
  + inversion H; subst; 
    destruct (IHMultiPar _ _ ltac:(auto)) as [B01 [B02 EQ]]; 
    auto; split_hyp; subst.
    exists B01, B02; repeat split; auto.
    eapply MP_Step; eauto.
    move: H3 => [L0 h].
    exists (L \u L0). move=> x Fr. repeat spec x.
    eapply MP_Step; eauto.
Qed. 

Lemma MultiPar_SSigma_inv : forall S D rho A B, MultiPar S D A B -> forall A1 A2,
      A = a_SSigma rho A1 A2 -> 
      exists B1 B2, B = (a_SSigma rho B1 B2)
               /\ MultiPar S D A1 B1 /\
               exists L, forall x, x \notin L -> 
                         MultiPar ([(x,D)] ++ S) D (open_tm_wrt_tm A2 (a_Var_f x)) 
                                  (open_tm_wrt_tm B2 (a_Var_f x)).
Proof.
  intros S D rho A B H. 
  induction H; intros; subst; try invert_Grade; subst.
  + eexists. eexists. split; try reflexivity. repeat split; eauto.
  + inversion H; subst; 
    destruct (IHMultiPar _ _ ltac:(auto)) as [B01 [B02 EQ]]; 
    auto; split_hyp; subst.
    exists B01, B02; repeat split; auto.
    eapply MP_Step; eauto.
    move: H3 => [L0 h].
    exists (L \u L0). move=> x Fr. repeat spec x.
    eapply MP_Step; eauto.
Qed. 


Lemma MultiPar_Sum_inv : forall S D A B, MultiPar S D A B -> forall A1 A2,
      A = a_Sum A1 A2 -> exists B1 B2, B = (a_Sum B1 B2)   /\ MultiPar S D A1 B1 /\ MultiPar S D A2 B2.
Proof.
  intros S D A B H.
  induction H; intros; subst; try invert_Grade; subst.
  + eexists. eexists. split; try reflexivity. repeat split; eauto.
  + inversion H; subst; 
    destruct (IHMultiPar _ _ ltac:(auto)) as [B01 [B02 EQ]]; auto; split_hyp; subst.
      exists B01, B02; eauto.
Qed.


(* ------------------------------------------------------------------------ *)

(* Proof that joinability implies consistency. *)

Ltac step_left := apply Consistent_a_Step_R; [auto |intro N; inversion N; inversion H0]; fail.
Ltac step_right := apply Consistent_a_Step_L; [auto | intro N; inversion N; inversion H0]; fail.

(* look for a multipar involvong a head form and apply the appropriate lemma for that
   head form. Note: for paths, the lemma has already been applied so we only need
   to look for a hypothesis about path consistency. *)
Ltac MultiPar_step EQ :=
  let b1' := fresh "b" in
  let b2' := fresh "b" in
  match goal with
  | [ SIDE : MultiPar _  _ ( a_Type _ ) _ |- _ ] =>
    eapply MultiPar_Type_inv in SIDE; eauto; rename SIDE into EQ
  | [ SIDE : MultiPar _  _ a_TyUnit _ |- _ ] =>
    apply MultiPar_TyUnit_inv in SIDE; auto; rename SIDE into EQ
  | [ SIDE : MultiPar _  _ (a_Pi _ _ _ ) _ |- _ ] =>
    destruct (MultiPar_Pi_inv SIDE ltac:(auto)) as [b1' [b2' [EQ _]]]; clear SIDE
  | [ SIDE : MultiPar _ _ (a_WSigma _ _ _)  _ |- _ ] =>
    destruct (MultiPar_WSigma_inv SIDE ltac:(auto)) as [b1' [b2' [EQ _]]]; clear SIDE
  | [ SIDE : MultiPar _ _ (a_SSigma _ _ _)  _ |- _ ] =>
    destruct (MultiPar_SSigma_inv SIDE ltac:(auto)) as [b1' [b2' [EQ _]]]; clear SIDE
  | [ SIDE : MultiPar _ _ (a_Sum _ _)  _ |- _ ] =>
    destruct (MultiPar_Sum_inv SIDE ltac:(auto)) as [b1' [b2' [EQ _]]]; clear SIDE
  end.


Lemma Joins_Consistent : forall S a psi b, Joins S psi a b -> Consistent a b.
Proof.
  intros.
  all: destruct H as [P psi a1 a2 b1 b2 MSL MSR].
  move: (MultiPar_lc1 MSL) => lc1.
  move: (MultiPar_lc1 MSR) => lc2.
  move: (MultiPar_lc2 MSL) => lc3.
  destruct a1; try step_left; destruct a2; try step_right; auto.
  (* 34 subgoals. At this point all cases have a value type form on both left and right. *)
  (* Resolve the MP of these type forms. *)
  all: try MultiPar_step EQ1.
  all: try MultiPar_step EQ2.

  all: subst; match goal with [H : GEq _ _ _ _ |- _ ] => inversion H; subst end.

  (* 4 cases that actually are consistent. *)
  all: repeat match goal with [H : lc_tm (_ _) |- _ ] => inversion H; subst; clear H end.
  all: eauto.
  
Qed. 


(*
a  -> b -->* c      d - by confluence
|     |      |      e - by induction
v     v      v
a2 -> d -->* e
*)

Lemma MultiPar_confluence_helper : forall S D a a1, MultiPar S D a a1
-> forall a2, Par S D a a2 -> exists e, Par S D a1 e /\ MultiPar S D a2 e.
Proof.
  intros S D a a1 H. induction H.
  - intros. move: (Par_lc2 H0) => cl1. exists a2. split; eauto.
    eapply MP_Refl; eauto using Par_Grade2.
  - intros. destruct (confluence H H1) as [d [L R]].
      destruct (IHMultiPar _ L) as [e [LL RR]]; auto.
      exists e. split; eauto.
Qed.

(*
a -->  b -->* c    d - by prior lemma
|      |      |    e - by induction.
v      v      v
*      *      *
a2 --> d -->* e
*)

Lemma MultiPar_confluence : forall S D a a1, MultiPar S D a a1
-> forall a2, MultiPar S D a a2 -> exists b1, exists b2,  MultiPar S D a1 b1 /\ MultiPar S D a2 b2 /\ GEq S D b1 b2.
Proof.
  intros S D a a1 MP. induction MP.
  intros.
 - exists a2. exists a2.
   repeat split; eauto using MultiPar_lc2, MultiPar_Grade2, GEq_refl.
 - intros.
   destruct (MultiPar_confluence_helper H0 H) as [d [L R]].
   destruct (IHMP d) as [e [f ?]]; auto. split_hyp.
   exists e. exists f. split; eauto.
Qed.


Lemma MultiPar_refl : forall S D a, Grade S D a -> MultiPar S D a a.
Proof.
  intros. eapply MP_Refl. auto.
Qed.

Lemma MultiPar_trans : forall S D a b c, MultiPar S D a b -> MultiPar S D b c -> MultiPar S D a c.
Proof.
  intros.
  induction H. auto.
  eauto.
Qed.


Lemma MultiPar_respects_GEq : forall W a psi b, MultiPar W psi a b -> forall a', GEq W psi a a' 
                                                                  -> exists b', MultiPar W psi a' b'
                                                                          /\ GEq W psi b b'.
Proof.
  induction 1; intros.
  - exists a'. split. eapply MP_Refl. eauto using GEq_lc2, GEq_Grade2. auto.
  - move: (Par_respects_GEq H H1) => [b1 [PP GE]].
    edestruct IHMultiPar as [b' [MP GE']]. eauto.
    eauto.
Qed. 


(*
    a   b   c        a         b         c
     \ / \ /          \      /  \       /
      ab  bc          ab = ab'   bc = bc' 
      .\ ./            |    |    |    |  
        d             d1 =  d  = e =  e1
 *)


Lemma Joins_transitive : forall S D a b, Joins S D a b -> forall c, Joins S D b c -> Joins S D a c.
Proof.
  intros S D a b h. destruct h as [P psi a b ab ab' MSL MSR].
  intros c h2. destruct h2 as [? ? b c bc bc' MSL' MSR'].
  destruct (MultiPar_confluence MSR MSL') as [d [e [MSL'' [MSR'' GE]]]].
  move: (GEq_symmetry H) => hsym.
  destruct (MultiPar_respects_GEq MSL'' hsym) as [d1 [h1 h2]].
  destruct (MultiPar_respects_GEq MSR'' H0) as [e1 [h3 h4]].
  apply join with (b1:= d1)(b2:=e1).
  eapply MultiPar_trans; eauto.
  eapply MultiPar_trans; eauto.
  eapply GEq_trans with (b:=d); eauto using GEq_symmetry.
  eapply GEq_trans with (b:=e); eauto using GEq_symmetry.
Qed. 

Lemma Joins_symmetry: forall S D a b, Joins S D a b -> Joins S D b a.
Proof.
  intros S D a b H.
  destruct H. 
  apply join with (b1:= b2)(b2:=b1); eauto using GEq_symmetry.
Qed.


Lemma Joins_refl : forall S D a, Grade S D a -> Joins S D a a.
Proof.
  intros.
  econstructor. eapply MP_Refl; auto. eapply MP_Refl; auto.
  eapply GEq_refl. eauto.
Qed. 

(* --------------------------------------------- *)


Lemma MultiPar_Pi :  forall (L : atoms) (P : econtext) (psi psi1 : grade) (A1 B1 A2 B2 : tm),
    MultiPar P psi A1 A2 ->
    (forall x : atom,
        x `notin` L -> MultiPar ([(x, psi)] ++ P) psi 
                               (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x))) ->
    MultiPar P psi (a_Pi psi1 A1 B1) (a_Pi psi1 A2 B2).
Proof.
  intros.
  eapply MultiPar_trans with (b := (_ psi1 A2 B1)). 
  + induction H; auto. 
    ++ eapply MP_Refl; eauto.
       fresh_apply_Grade x; auto; repeat spec x.
       eauto using MultiPar_Grade1.
    ++ eapply MP_Step with (b := _ psi1 b B1); eauto.
       fresh_apply_Par x; eauto; repeat spec x.
       eapply Par_Refl; eauto using MultiPar_Grade1.
  + pick fresh x. repeat spec x.
    dependent induction H1.
    ++ apply open_tm_wrt_tm_inj in x; auto. subst.
       eapply MP_Refl; eauto.
       fresh_apply_Grade y; eauto 2 using MultiPar_Grade2.
       eapply (@Grade_renaming x0); auto.
    ++ eapply MP_Step with (b := a_Pi psi1 A2 (close_tm_wrt_tm x b)).
       fresh_apply_Par y. eapply Par_Refl; eauto using MultiPar_Grade2.
       rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm b x) in H0.
       eapply (@Par_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto.
       eapply IHMultiPar;  try rewrite fv_tm_tm_close_tm_wrt_tm; eauto 3.
       rewrite (open_tm_wrt_tm_close_tm_wrt_tm b x).
       auto.
Qed.

Lemma MultiPar_WSigma
     : forall (L : atoms) (P : econtext) (psi psi1 : grade) (A1 B1 A2 B2 : tm),
       MultiPar P psi A1 A2 ->
       (forall x : atom,
        x `notin` L -> MultiPar ([(x,psi)] ++ P) psi (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x))) ->
       MultiPar P psi (a_WSigma psi1 A1 B1) (a_WSigma psi1 A2 B2).
Proof.
  intros.
  eapply MultiPar_trans with (b := (_ psi1 A2 B1)). 
  + induction H; auto. 
    ++ eapply MP_Refl; eauto.
       fresh_apply_Grade x; auto; repeat spec x.
       eauto using MultiPar_Grade1.
    ++ eapply MP_Step with (b := _ psi1 b B1); eauto.
       fresh_apply_Par x; eauto; repeat spec x.
       eapply Par_Refl; eauto using MultiPar_Grade1.
  + pick fresh x. repeat spec x.
    dependent induction H1.
    ++ apply open_tm_wrt_tm_inj in x; auto. subst.
       eapply MP_Refl; eauto.
       fresh_apply_Grade y; eauto 2 using MultiPar_Grade2.
       eapply (@Grade_renaming x0); auto.
    ++ eapply MP_Step with (b := a_WSigma psi1 A2 (close_tm_wrt_tm x b)).
       fresh_apply_Par y. eapply Par_Refl; eauto using MultiPar_Grade2.
       rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm b x) in H0.
       eapply (@Par_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto.
       eapply IHMultiPar;  try rewrite fv_tm_tm_close_tm_wrt_tm; eauto 3.
       rewrite (open_tm_wrt_tm_close_tm_wrt_tm b x).
       auto.
Qed.


Lemma MultiPar_SSigma
     : forall (L : atoms) (P : econtext) (psi psi1 : grade) (A1 B1 A2 B2 : tm),
       MultiPar P psi A1 A2 ->
       (forall x : atom,
        x `notin` L -> MultiPar ([(x, psi)] ++ P) psi (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B2 (a_Var_f x))) ->
       MultiPar P psi (a_SSigma psi1 A1 B1) (a_SSigma psi1 A2 B2).
Proof.
  intros.
  eapply MultiPar_trans with (b := (_ psi1 A2 B1)). 
  + induction H; auto. 
    ++ eapply MP_Refl; eauto.
       fresh_apply_Grade x; auto; repeat spec x.
       eauto using MultiPar_Grade1.
    ++ eapply MP_Step with (b := _ psi1 b B1); eauto.
       fresh_apply_Par x; eauto; repeat spec x.
       eapply Par_Refl; eauto using MultiPar_Grade1.
  + pick fresh x. repeat spec x.
    dependent induction H1.
    ++ apply open_tm_wrt_tm_inj in x; auto. subst.
       eapply MP_Refl; eauto.
       fresh_apply_Grade y; eauto 2 using MultiPar_Grade2.
       eapply (@Grade_renaming x0); auto.
    ++ eapply MP_Step with (b := a_SSigma psi1 A2 (close_tm_wrt_tm x b)).
       fresh_apply_Par y. eapply Par_Refl; eauto using MultiPar_Grade2.
       rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm b x) in H0.
       eapply (@Par_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto.
       eapply IHMultiPar;  try rewrite fv_tm_tm_close_tm_wrt_tm; eauto 3.
       rewrite (open_tm_wrt_tm_close_tm_wrt_tm b x).
       auto.
Qed.

Lemma MultiPar_Abs1 : forall (L : atoms) (P : econtext) (psi psi0 : grade) (A1 b1 b2 : tm),
       (forall x : atom,
        x `notin` L -> MultiPar ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))) ->
       CGrade P psi q_Top A1 ->
       MultiPar P psi (a_Abs psi0 A1 b1) (a_Abs psi0 A1 b2).
Proof.
  intros.
  pick fresh x. repeat spec x.
  dependent induction H1.
    ++ apply open_tm_wrt_tm_inj in x; auto. subst.
       eapply MP_Refl; eauto.
       fresh_apply_Grade y; eauto 2 using MultiPar_Grade2.
       eapply (@Grade_renaming x0); auto.
    ++ eapply MP_Step with (b := a_Abs psi0 A1 (close_tm_wrt_tm x b)).
       fresh_apply_Par y. 
       rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm b x) in H.
       eapply (@Par_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto.       
       inversion H0; eauto.
       eapply IHMultiPar;  try rewrite fv_tm_tm_close_tm_wrt_tm; eauto 3.
       rewrite (open_tm_wrt_tm_close_tm_wrt_tm b x).
       auto.
Qed.

Inductive CMultiPar : econtext -> grade -> grade -> tm -> tm -> Prop :=
    CMultiPar_Leq : forall (P : econtext) (psi psi0 : grade) (a1 a2 : tm),
               psi0 <= psi -> MultiPar P psi a1 a2 -> CMultiPar P psi psi0 a1 a2
  | CMultiPar_Nleq : forall (P : econtext) (psi psi0 : grade) (a1 a2 : tm),
                lc_tm a1 ->
                lc_tm a2 -> ~ psi0 <= psi -> uniq P -> CMultiPar P psi psi0 a1 a2.

Hint Constructors CMultiPar : core.

Lemma MultiPar_Abs : forall (L : atoms) (P : econtext) (psi psi0 : grade) (A1 A2 b1 b2 : tm),
       (forall x : atom,
        x `notin` L -> MultiPar ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))) ->
       (CMultiPar P psi q_Top A1 A2) ->
       MultiPar P psi (a_Abs psi0 A1 b1) (a_Abs psi0 A2 b2).
Proof.
  intros.
  inversion H0; subst; clear H0.
  + induction H2; eauto. eapply MultiPar_Abs1; eauto.
    eapply MP_Step with (b := a_Abs psi0 b b1). 
    fresh_apply_Par y; auto. spec y. eapply Par_Refl. eapply MultiPar_Grade1; eauto.
    eapply IHMultiPar; eauto.
  + eapply MP_Step with (b := a_Abs psi0 A2 b1).  
    fresh_apply_Par y; auto. spec y. eapply Par_Refl. eapply MultiPar_Grade1; eauto.
    eapply MultiPar_Abs1; eauto.
Qed.


Lemma MultiPar_WPairBeta
     : forall (L : atoms) (P : econtext) (psi psi0 phi : grade) (a1 b1 b2 a1' a2' : tm),
       MultiPar P psi a1 (a_WPair a1' psi0 a2') ->
       (forall x : atom,
        x `notin` L -> MultiPar ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))) ->
       MultiPar P psi (a_LetPair psi0 a1 b1) (a_App (open_tm_wrt_tm b2 a1') q_Bot a2').
Proof.
  intros.
  eapply MultiPar_trans with (b := a_LetPair psi0 a1 b2).
  + pick fresh x. repeat spec x.
    dependent induction H1.
    ++ apply open_tm_wrt_tm_inj in x; auto. subst.
       eapply MP_Refl; eauto.
       fresh_apply_Grade y; eauto 2 using MultiPar_Grade1.
       eapply (@Grade_renaming x0); auto.
    ++ eapply MP_Step with (b := a_LetPair psi0 a1 (close_tm_wrt_tm x b)).
       fresh_apply_Par y. eapply Par_Refl; eauto using MultiPar_Grade1.
       rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm b x) in H0.
       eapply (@Par_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto.
       eapply IHMultiPar;  try rewrite fv_tm_tm_close_tm_wrt_tm; eauto 3.
       rewrite (open_tm_wrt_tm_close_tm_wrt_tm b x).
       auto.
  + dependent induction H; auto. 
    ++ eapply MP_Step with (b :=  (a_App (open_tm_wrt_tm b2 a1') q_Bot a2')).
       fresh_apply_Par x; auto. spec x.
       eapply Par_Refl.
       eapply MultiPar_Grade2; eauto.
       eapply MP_Refl; eauto.
       have GA: (Grade P psi (open_tm_wrt_tm b2 a1')).
       { 
         pick fresh x. spec x.
         invert_Grade; subst. invert_CGrade a1'; subst.
         eapply Grade_open; eauto using MultiPar_Grade2.
         eapply Grade_open_irrel; eauto using MultiPar_Grade2.
       }
       invert_Grade; subst. 
       eapply G_App; eauto using leq_Bot.
    ++ eapply MP_Step with (b := a_LetPair psi0 b b2).
       fresh_apply_Par x; eauto; repeat spec x.
       eapply Par_Refl; eauto using MultiPar_Grade2.
       eapply IHMultiPar; eauto.
Qed.

Lemma MultiPar_LetPair
     : forall (L : atoms) (P : econtext) (psi psi0 phi : grade) (a1 b1 a2 b2 : tm),
       MultiPar P psi a1 a2 ->
       (forall x : atom,
        x `notin` L -> MultiPar ([(x, psi0)] ++ P) psi (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))) ->
       MultiPar P psi (a_LetPair psi0 a1 b1) (a_LetPair psi0 a2 b2).
Proof.
  intros.
  eapply MultiPar_trans with (b := a_LetPair psi0 a1 b2).
  + pick fresh x. repeat spec x.
    dependent induction H1.
    ++ apply open_tm_wrt_tm_inj in x; auto. subst.
       eapply MP_Refl; eauto.
       fresh_apply_Grade y; eauto 2 using MultiPar_Grade1.
       eapply (@Grade_renaming x0); auto.
    ++ eapply MP_Step with (b := a_LetPair psi0 a1 (close_tm_wrt_tm x b)).
       fresh_apply_Par y. eapply Par_Refl; eauto using MultiPar_Grade1.
       rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm b x) in H0.
       eapply (@Par_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto.
       eapply IHMultiPar;  try rewrite fv_tm_tm_close_tm_wrt_tm; eauto 3.
       rewrite (open_tm_wrt_tm_close_tm_wrt_tm b x).
       auto.
  + induction H.
    ++ eapply MP_Refl.
       fresh_apply_Grade x; eauto 3 using MultiPar_Grade2.
    ++ eapply MP_Step with (b := a_LetPair psi0 b b2).
       fresh_apply_Par x; eauto 4 using MultiPar_Grade2.
       eapply IHMultiPar; eauto.
Qed.

Ltac fresh_apply_MultiPar x := 
  match goal with 
      | [ |- MultiPar ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply MultiPar_Pi
      | [ |- MultiPar ?P ?psi (a_WSigma ?psi2 ?a ?b) (a_WSigma ?psi3 ?a3 ?b3) ] => pick fresh x and apply MultiPar_WSigma
      | [ |- MultiPar ?P ?psi (a_SSigma ?psi2 ?a ?b) (a_SSigma ?psi3 ?a2 ?b2) ] => pick fresh x and apply MultiPar_SSigma
      | [ |- MultiPar ?P ?psi (a_Abs ?psi2 ?A1 ?b) (a_Abs ?psi3 ?A2 ?b3) ] => pick fresh x and apply MultiPar_Abs
      | [ |- MultiPar ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_App ?a1 ?phi2 ?a2)  ] => pick fresh x and apply MultiPar_WPairBeta
      | [ |- MultiPar ?P ?psi (a_LetPair ?psi2 ?a ?b) (a_LetPair ?psi3 ?a2 ?b2)  ] => pick fresh x and apply MultiPar_LetPair
    end.

Ltac exists_apply_MultiPar x :=
  let y := fresh in
  fresh_apply_MultiPar y; eauto;
  eapply (@MultiPar_renaming x); try rewrite fv_tm_tm_close_tm_wrt_tm; auto;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.

(*
Lemma MultiPar_Pi_exists :  forall x (P : econtext) (psi psi1 : grade) (A1 B1 A2 B' : tm),
    x `notin` fv_tm_tm B1 \u dom P -> 
    MultiPar P psi A1 A2 ->
    MultiPar ([(x, q_C)] ++ P) psi (open_tm_wrt_tm B1 (a_Var_f x)) B' ->
    MultiPar P psi (a_Pi psi1 A1 B1) (a_Pi psi1 A2 (close_tm_wrt_tm x B')).
Proof.
  intros x P psi psi1 A1 B1 A2 B' Fr MPA MPB.
  exists_apply_MultiPar x.
Qed.*)

Lemma MultiPar_PiFst : forall W rho (A B A' B' : tm) psi,
    MultiPar W psi (a_Pi rho A B) (a_Pi rho A' B') ->
    MultiPar W psi A A'.
Proof.
  intros W rho A B A' B' R' h1.
  dependent induction h1.
  - inversion H. subst. constructor. auto.
  - inversion H. subst. eapply IHh1; eauto.
    apply MP_Step with (b := A2). auto.
    eapply IHh1; eauto.
Qed.

(*
Lemma MultiPar_PiSnd : forall W rho (A B A' B' : tm) psi,
    MultiPar W psi (a_Pi rho A B) (a_Pi rho A' B') ->
    exists L, forall x, x `notin` L ->
              MultiPar ([(x,psi)] ++ W) psi (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)).
Proof.
  intros W rho A B A' B' R' h1.
  dependent induction h1; eauto.
  - inversion H. subst. exists L. intros.
    constructor. eauto.
  - inversion H; subst.
    eapply IHh1; eauto.
    destruct (IHh1 rho A2 B2 A' B') as [L0 h0]; auto.
    exists (L \u L0 \u dom P);  eauto.
Qed. *)


Lemma MultiPar_App : forall a a' c c' S psi psi0, 
    MultiPar S psi a c 
    -> CMultiPar S psi psi0 a' c' 
    -> MultiPar S psi (a_App a psi0 a') (a_App c psi0 c').
Proof.
  intros.
  eapply MultiPar_trans with (b:= a_App c psi0 a').
  + induction H. eapply MP_Refl; eauto.
    eapply G_App; eauto. inversion H0; subst; eauto using MultiPar_Grade1.
    eapply MP_Step with (b:= a_App b psi0 a'); eauto using MultiPar_Grade1.  
    eapply Par_App; eauto. inversion H0; subst; eauto using MultiPar_Grade1.
  + inversion H0; subst; clear H0. 
    induction H2; eauto using MultiPar_Grade2.
    eapply MP_Step with (b:= a_App c psi0 b); eauto using MultiPar_Grade2.  
    induction H; eauto using MultiPar_Grade2.
    eapply MP_Step with (b:= a_App a psi0 c'); eauto using MultiPar_Grade2.  
    
Qed.    

(*
Lemma MultiPar_AppRel : forall a a' c c' S psi psi0, 
    MultiPar S psi a c 
    -> MultiPar S psi a' c' 
    -> psi0 <= psi 
    -> MultiPar S psi (a_App a psi0 a') (a_App c psi0 c').
Proof.
  intros.
  eapply MultiPar_trans with (b:= a_App c psi0 a').
  + induction H; eauto using MultiPar_Grade1. 
    eapply MP_Step with (b:= a_App b psi0 a'); eauto using MultiPar_Grade1.  
  + induction H0; eauto using MultiPar_Grade2.
    eapply MP_Step with (b:= a_App c psi0 b); eauto using MultiPar_Grade2.  
Qed.    
*)

Lemma Joins_App : forall a a' b b' S psi psi0, 
      Joins S psi a b 
    -> CJoins S psi psi0 a' b' 
    -> Joins S psi (a_App a psi0 a') (a_App b psi0 b').
Proof.
  intros a a' b b' S psi psi0 H H0.
  inversion H.
  inversion H0. inversion H9; subst.
  + apply join with (b1:= (a_App b1 psi0 b0)) (b2:= a_App b2 psi0 b3).
    eapply MultiPar_App; eauto. 
    eapply MultiPar_App; auto. 
    apply GEq_App; eauto.
  +  apply join with (b1:= (a_App b1 psi0 a')) (b2:= a_App b2 psi0 b').
     eapply MultiPar_App; eauto. 
     eapply MultiPar_App; auto. 
     apply GEq_App; eauto using GEq_uniq.
Qed.


Lemma Joins_AppRel: forall a a' b b' S psi psi0, 
      Joins S psi a b 
    -> Joins S psi a' b' 
    -> psi0 <= psi
    -> Joins S psi (a_App a psi0 a') (a_App b psi0 b').
Proof.
  intros a a' b b' S psi psi0 H H0 LE.
  inversion H.
  inversion H0.
  subst.
  apply join with (b1:= (a_App b1 psi0 b0)) (b2:= a_App b2 psi0 b3).
  eapply MultiPar_App; eauto. 
  eapply MultiPar_App; auto. 
  apply GEq_App; eauto.
Qed.

Lemma Joins_AppIrrel : forall a a' c c' S psi psi0, 
      Joins S psi a c 
    -> lc_tm a'
    -> lc_tm c'
    -> not (psi0 <= psi)
    -> Joins S psi (a_App a psi0 a') (a_App c psi0 c').
Proof.
  intros a a' b b' S psi psi0 H LC1 LC2 NLE.
  inversion H.
  subst.
  apply join with (b1:= (a_App b1 psi0 a')) (b2:= a_App b2 psi0 b').
  eapply MultiPar_App; eauto using GEq_uniq.
  eapply MultiPar_App; eauto using GEq_uniq.
  apply GEq_App; eauto using GEq_uniq.
Qed.  

Lemma MultiPar_WPairRel : forall a a' b b' S psi psi0, 
      MultiPar S psi a b 
    -> psi0 <= psi
    -> MultiPar S psi a' b' 
    -> MultiPar S psi (a_WPair a psi0 a') (a_WPair b psi0 b').
Proof.
  intros a a' b b' S psi psi0 MP LE MP2.
  + eapply MultiPar_trans with (b:= a_WPair b psi0 a').
    ++ induction MP; eauto using MultiPar_Grade1.
       eapply MP_Step with (b:= a_WPair b psi0 a'); eauto using MultiPar_Grade1.  
    ++ induction MP2; eauto using MultiPar_Grade1.
       eapply MP_Step with (b:= a_WPair b psi0 a0); eauto using MultiPar_Grade2.
       eapply MP_Step with (b:= a_WPair b psi0 b0); eauto using MultiPar_Grade2.
Qed.

Lemma MultiPar_WPairIrrel : forall a a' b b' S psi psi0, 
      lc_tm a 
    -> lc_tm b
    -> not (psi0 <= psi)
    -> MultiPar S psi a' b' 
    -> MultiPar S psi (a_WPair a psi0 a') (a_WPair b psi0 b').
Proof.
  intros a a' b b' S psi psi0 LC1 LC2 NLE MP2.
  + eapply MultiPar_trans with (b:= a_WPair b psi0 a').
    ++ eapply MP_Step with (b:= a_WPair b psi0 a').
       eapply Par_WPair; eauto using MultiPar_Grade1, MultiPar_uniq.
       eapply MP_Refl; eauto using MultiPar_Grade1, MultiPar_uniq.
    ++ induction MP2. 
       eapply MP_Refl; eauto using MultiPar_Grade1, MultiPar_uniq.
       eapply MP_Step with (b:= a_WPair b psi0 b0); eauto.
       eapply Par_WPair; eauto using MultiPar_Grade1, MultiPar_uniq.
Qed.


Lemma Joins_WPair : forall a a' b b' S psi psi0, 
      CJoins S psi psi0 a b 
    -> Joins S psi a' b' 
    -> Joins S psi (a_WPair a psi0 a') (a_WPair b psi0 b').
Proof.
  intros a a' b b' S psi psi0 H H0.
  inversion H; inversion H0; subst.
  + inversion H2; subst. 
    apply join with (b1:= (a_WPair b0 psi0 b1)) (b2:= a_WPair b3 psi0 b2).
    eapply MultiPar_WPairRel; eauto. 
    eapply MultiPar_WPairRel; eauto. 
    apply GEq_WPair; eauto.
  + eapply join with (b1 := (a_WPair a psi0 b1)) (b2:= a_WPair b psi0 b2).
    eapply MultiPar_WPairIrrel; eauto. 
    eapply MultiPar_WPairIrrel; eauto. 
    apply GEq_WPair; eauto.    
Qed.

Lemma MultiPar_SPairRel : forall a a' b b' S psi psi0, 
      MultiPar S psi a b 
    -> psi0 <= psi
    -> MultiPar S psi a' b' 
    -> MultiPar S psi (a_SPair a psi0 a') (a_SPair b psi0 b').
Proof.
  intros a a' b b' S psi psi0 MP LE MP2.
  + eapply MultiPar_trans with (b:= a_SPair b psi0 a').
    ++ induction MP; eauto using MultiPar_Grade1.
       eapply MP_Step with (b:= a_SPair b psi0 a'); eauto using MultiPar_Grade1.  
    ++ induction MP2; eauto using MultiPar_Grade1.
       eapply MP_Step with (b:= a_SPair b psi0 a0); eauto using MultiPar_Grade2.
       eapply MP_Step with (b:= a_SPair b psi0 b0); eauto using MultiPar_Grade2.
Qed.

Lemma MultiPar_SPairIrrel : forall a a' b b' S psi psi0, 
      lc_tm a 
    -> lc_tm b
    -> not (psi0 <= psi)
    -> MultiPar S psi a' b' 
    -> MultiPar S psi (a_SPair a psi0 a') (a_SPair b psi0 b').
Proof.
  intros a a' b b' S psi psi0 LC1 LC2 NLE MP2.
  + eapply MultiPar_trans with (b:= a_SPair b psi0 a').
    ++ eapply MP_Step with (b:= a_SPair b psi0 a').
       eapply Par_SPair; eauto using MultiPar_Grade1, MultiPar_uniq.
       eapply MP_Refl; eauto using MultiPar_Grade1, MultiPar_uniq.
    ++ induction MP2. 
       eapply MP_Refl; eauto using MultiPar_Grade1, MultiPar_uniq.
       eapply MP_Step with (b:= a_SPair b psi0 b0); eauto.
       eapply Par_SPair; eauto using MultiPar_Grade1, MultiPar_uniq.
Qed.

Lemma Joins_SPair : forall a a' b b' S psi psi0, 
      CJoins S psi psi0 a b 
    -> Joins S psi a' b' 
    -> Joins S psi (a_SPair a psi0 a') (a_SPair b psi0 b').
Proof.
  intros a a' b b' S psi psi0 H H0.
  inversion H; inversion H0; subst.
  + inversion H2; subst. 
    apply join with (b1:= (a_SPair b0 psi0 b1)) (b2:= a_SPair b3 psi0 b2).
    eapply MultiPar_SPairRel; eauto. 
    eapply MultiPar_SPairRel; eauto. 
    apply GEq_SPair; eauto.
  + eapply join with (b1 := (a_SPair a psi0 b1)) (b2:= a_SPair b psi0 b2).
    eapply MultiPar_SPairIrrel; eauto. 
    eapply MultiPar_SPairIrrel; eauto. 
    apply GEq_SPair; eauto.    
Qed.


Lemma MultiPar_Proj1 : forall P a1 a2 psi0 psi, 
    MultiPar P psi a1 a2 ->
    psi0 <= psi -> 
    MultiPar P psi (a_Proj1 psi0 a1) (a_Proj1 psi0 a2).
Proof.
  induction 1; intros.
  eapply MP_Refl; eauto.
  eapply MP_Step. 2: { eauto. }
  eapply Par_Proj1; eauto.
Qed.

Lemma Joins_Proj1 : forall P a1 a2 psi0 psi, 
    Joins P psi a1 a2 ->
    psi0 <= psi -> 
    Joins P psi (a_Proj1 psi0 a1) (a_Proj1 psi0 a2).
Proof. 
  intros.
  inversion H. subst.
  eapply join.
  eapply MultiPar_Proj1; eauto.
  eapply MultiPar_Proj1; eauto.
  eapply GEq_Proj1; eauto.
Qed.

Lemma MultiPar_Proj2 : forall P a1 a2 psi0 psi, 
    MultiPar P psi a1 a2 ->
    MultiPar P psi (a_Proj2 psi0 a1) (a_Proj2 psi0 a2).
Proof.
  induction 1; intros.
  eapply MP_Refl; eauto.
  eapply MP_Step. 2: { eauto. }
  eapply Par_Proj2; eauto.
Qed.

Lemma Joins_Proj2 : forall P a1 a2 psi0 psi, 
    Joins P psi a1 a2 ->
    Joins P psi (a_Proj2 psi0 a1) (a_Proj2 psi0 a2).
Proof. 
  intros.
  inversion H. subst.
  eapply join.
  eapply MultiPar_Proj2; eauto.
  eapply MultiPar_Proj2; eauto.
  eapply GEq_Proj2; eauto.
Qed.

Lemma MultiPar_Sum : forall P psi A1 A1' A2 A2',  MultiPar P psi A1 A1' ->
  MultiPar P psi A2 A2' ->
  MultiPar P psi (a_Sum A1 A2) (a_Sum A1' A2').
Proof.
  intros.
  eapply MultiPar_trans with (b := a_Sum A1' A2).
  + induction H; eauto using MultiPar_Grade1. 
    eapply MP_Step with (b:= a_Sum b A2); eauto using MultiPar_Grade1.
  + induction H0; eauto using MultiPar_Grade2.
    eapply MP_Step with (b:= a_Sum A1' b); eauto using MultiPar_Grade2.
Qed.

Lemma Joins_Sum : forall P psi A1 A1' A2 A2',  Joins P psi A1 A1' ->
  Joins P psi A2 A2' ->
  Joins P psi (a_Sum A1 A2) (a_Sum A1' A2').
Proof.
  intros.
  inversion H. inversion H0. subst.
  eapply join; eauto using MultiPar_Sum.
Qed.

Lemma MultiPar_Inj1 : forall P a1 a2 psi, 
    MultiPar P psi a1 a2 ->
    MultiPar P psi (a_Inj1 a1) (a_Inj1 a2).
Proof.
  induction 1; intros.
  eapply MP_Refl; eauto.
  eapply MP_Step. 2: { eauto. }
  eapply Par_Inj1; eauto.
Qed.

Lemma Joins_Inj1 : forall P a1 a2 psi, 
    Joins P psi a1 a2 ->
    Joins P psi (a_Inj1 a1) (a_Inj1 a2).
Proof. 
  intros.
  inversion H. subst.
  eapply join.
  eapply MultiPar_Inj1; eauto.
  eapply MultiPar_Inj1; eauto.
  eapply GEq_Inj1; eauto.
Qed.

Lemma MultiPar_Inj2 : forall P a1 a2 psi, 
    MultiPar P psi a1 a2 ->
    MultiPar P psi (a_Inj2 a1) (a_Inj2 a2).
Proof.
  induction 1; intros.
  eapply MP_Refl; eauto.
  eapply MP_Step. 2: { eauto. }
  eapply Par_Inj2; eauto.
Qed.

Lemma Joins_Inj2 : forall P a1 a2 psi, 
    Joins P psi a1 a2 ->
    Joins P psi (a_Inj2 a1) (a_Inj2 a2).
Proof. 
  intros.
  inversion H. subst.
  eapply join.
  eapply MultiPar_Inj2; eauto.
  eapply MultiPar_Inj2; eauto.
  eapply GEq_Inj2; eauto.
Qed.


Lemma Joins_Case : forall P a a' b1 b1' b2 b2' psi0 psi, 
    psi0 <= psi ->
    Joins P psi a a' -> 
    Joins P psi b1 b1' -> 
    Joins P psi b2 b2' -> 
    Joins P psi (a_Case psi0 a b1 b2) (a_Case psi0 a' b1' b2'). 
Proof.
  intros.
  inversion H0. inversion H1. inversion H2. subst.
  have MultiPar_Case : forall a b0 b1 b4 b2 b6, 
    MultiPar P psi a b0 ->
    MultiPar P psi b1 b4 -> 
    MultiPar P psi b2 b6 ->
    psi0 <= psi ->
    MultiPar P psi (a_Case psi0 a b1 b2) (a_Case psi0 b0 b4 b6).
  { clear. intros.
    move: (MultiPar_Grade1 H) => G1.
    move: (MultiPar_Grade1 H) => G2.
    move: (MultiPar_Grade1 H0) => G10.
    move: (MultiPar_Grade2 H0) => G20.
    move: (MultiPar_Grade1 H1) => G11.
    move: (MultiPar_Grade2 H1) => G21.
    eapply MultiPar_trans with (b:= a_Case psi0 b0 b1 b2).
    2: eapply MultiPar_trans with (b := a_Case psi0 b0 b4 b2).
    + induction H; eauto. 
      eapply MP_Step. eapply Par_Case; eauto using Par_Grade2.
      eapply IHMultiPar; eauto using Par_Grade2.
    + induction H0; eauto using MultiPar_Grade2. 
      eapply MP_Step. 2:  eapply IHMultiPar; eauto using Par_Grade2.
      eapply Par_Case; eauto using MultiPar_Grade2.
    + induction H1; eauto using MultiPar_Grade2.
      eapply MP_Step. 2:  eapply IHMultiPar; eauto using Par_Grade2.
      eapply Par_Case; eauto using MultiPar_Grade2.
  }
  eapply join.
  eapply MultiPar_Case; eauto.
  eapply MultiPar_Case; eauto.
  eapply GEq_Case; eauto.
Qed.

(* This is the key lemma for consistency. If we can prove two types equal, then they are joinable. *)
(* Basically, we need to prove a joins version of every DefEq rule. *)

Ltac invert_Joins := 
    match goal with [H : Joins _ _ _ _ |- _ ] => inversion H; clear H; subst
                 |  [H : CJoins _ _ _ _ _ |- _ ] => inversion H; clear H; subst end.

Ltac invert_CJoins := 
    match goal with 
                 |  [H : CJoins _ _ _ _ _ |- _ ] => inversion H; clear H; subst end.


Ltac exists_apply_GEq x :=
  let y := fresh in 
  fresh_apply_GEq y; eauto;
  eapply (@GEq_renaming x); repeat rewrite fv_tm_tm_close_tm_wrt_tm; eauto;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm;
  rewrite open_tm_wrt_tm_close_tm_wrt_tm;
  auto.


Lemma DefEq_Joins : 
(forall S D phi A B, CDefEq S D phi A B -> CJoins S D phi A B) /\
forall S D A B, DefEq S D A B -> Joins S D A B.
Proof.
  apply CDefEq_DefEq_mutual.
  all: intros; eauto.
  - eapply Joins_refl; eauto.
  - eapply Joins_transitive; eauto.
  - eapply Joins_symmetry; eauto.
  - have MPb: MultiPar P psi b b.
    { eapply MP_Refl; eauto using Step_lc2, Step_Grade. }
    have MP: MultiPar P psi a b.
    { eapply MP_Step. eapply Step_Par; eauto. auto. }
    eapply join; eauto.
    eapply GEq_refl.
    eapply Step_Grade; eauto.
  - (* Pi cong *)
    pick fresh x. repeat spec x.
    repeat invert_Joins.
    eapply join with (b1 := a_Pi psi0 b0 (close_tm_wrt_tm x b1)) 
                     (b2 := a_Pi psi0 b3 (close_tm_wrt_tm x b2)).
    exists_apply_MultiPar x.
    exists_apply_MultiPar x.
    exists_apply_GEq x.
  - (* Abs cong *)
    pick fresh x. repeat spec x.
    repeat invert_Joins.
    + eapply join with (b1 := a_Abs psi0 b4 (close_tm_wrt_tm x b0)) 
                     (b2 := a_Abs psi0 b5 (close_tm_wrt_tm x b3)).
      exists_apply_MultiPar x.
      exists_apply_MultiPar x.
      exists_apply_GEq x.
    + eapply join with (b1 := a_Abs psi0 A1 (close_tm_wrt_tm x b0)) 
                     (b2 := a_Abs psi0 A2 (close_tm_wrt_tm x b3)).
      exists_apply_MultiPar x.
      exists_apply_MultiPar x.
      exists_apply_GEq x.
  - (* app cong *)
    invert_CJoins.
    eapply Joins_AppRel; eauto.
    eapply Joins_AppIrrel; eauto.
  - (* PiFst *)
    invert_Joins.
    eapply MultiPar_Pi_inv in H0; try reflexivity.
    move: H0 => [A1' [B1' [? hh]]]. split_hyp. subst. 
    eapply MultiPar_Pi_inv in H1; try reflexivity.
    move: H1 => [A2' [B2' [? hh]]]. split_hyp. subst. 
    match goal with [H:GEq _ _ _ _ |- _ ] => inversion H end. subst.
    eapply join; eauto.
  - (* PiSnd *)
    repeat invert_Joins.
    match goal with [H0 : MultiPar _ _ (a_Pi _ _ _) _ |- _ ] => 
        eapply MultiPar_Pi_inv in H0; try reflexivity;
        move: H0 => [A1' [B1' [? [? hh]]]]; subst; move: hh => [L1 h1] end.
    match goal with [H0 : MultiPar _ _ (a_Pi _ _ _) _ |- _ ] => 
        eapply MultiPar_Pi_inv in H0; try reflexivity;
        move: H0 => [A2' [B2' [? [? hh]]]]; subst; move: hh => [L2 h2] end.
    invert_GEq. subst.
    pick fresh x. repeat spec x.
    rewrite (subst_tm_tm_intro x B1); eauto.
    rewrite (subst_tm_tm_intro x B2); eauto.
    eapply join.
    eapply MultiPar_subst3; try eassumption.
    eapply MultiPar_subst3; try eassumption.
    move: CEq_GEq_equality_substitution => [_ sub].
    eapply sub with (P2 := nil); simpl_env; eauto.
    eapply CEq_Leq; eauto using MultiPar_lc2. reflexivity.
  - (* WSigma cong *)
    pick fresh x. repeat spec x.
    repeat invert_Joins.
    eapply join with (b1 := a_WSigma psi0 b0 (close_tm_wrt_tm x b1)) 
                     (b2 := a_WSigma psi0 b3 (close_tm_wrt_tm x b2)).
    exists_apply_MultiPar x.
    exists_apply_MultiPar x.
    exists_apply_GEq x.
  - (* WSigma Fst *)
    repeat invert_Joins.
    match goal with [H0 : MultiPar _ _ (a_WSigma _ _ _) _ |- _ ] => 
        eapply MultiPar_WSigma_inv in H0; try reflexivity;
        move: H0 => [A1' [B1' [? [? hh]]]]; subst; move: hh => [L1 h1] end.
    match goal with [H0 : MultiPar _ _ (a_WSigma _ _ _) _ |- _ ] => 
        eapply MultiPar_WSigma_inv in H0; try reflexivity;
        move: H0 => [A2' [B2' [? [? hh]]]]; subst; move: hh => [L2 h2] end.
    match goal with [H:GEq _ _ _ _ |- _ ] => inversion H end. subst.
    eapply join; eauto.
  - (* WSigma Snd *)
    repeat invert_Joins.
    match goal with [H0 : MultiPar _ _ (a_WSigma _ _ _) _ |- _ ] => 
        eapply MultiPar_WSigma_inv in H0; try reflexivity;
        move: H0 => [A1' [B1' [? [? hh]]]]; subst; move: hh => [L1 h1] end.
    match goal with [H0 : MultiPar _ _ (a_WSigma _ _ _) _ |- _ ] => 
        eapply MultiPar_WSigma_inv in H0; try reflexivity;
        move: H0 => [A2' [B2' [? [? hh]]]]; subst; move: hh => [L2 h2] end.
    match goal with [H:GEq _ _ _ _ |- _ ] => inversion H; clear H end. subst.
    pick fresh x. repeat spec x.
    rewrite (subst_tm_tm_intro x B1); eauto.
    rewrite (subst_tm_tm_intro x B2); eauto.
    eapply join.
    eapply MultiPar_subst3; try eassumption.
    eapply MP_Refl; eauto.
    eapply MultiPar_subst3; try eassumption.
    eapply MP_Refl; eauto.
    eapply GEq_substitution_same with (P2 := nil); eauto.
  - (* WPair *)
    eapply Joins_WPair; eauto.
  - (* LetPair cong *)
    pick fresh x. repeat spec x.
    repeat invert_Joins.
    eapply join with (b1 := a_LetPair psi0 b4 (close_tm_wrt_tm x b0)) 
                     (b2 := a_LetPair psi0 b5 (close_tm_wrt_tm x b3)).
    exists_apply_MultiPar x.
    exists_apply_MultiPar x.
    exists_apply_GEq x.
  - (* SSigma cong *)
    pick fresh x. repeat spec x.
    repeat invert_Joins.
    eapply join with (b1 := a_SSigma psi0 b0 (close_tm_wrt_tm x b1)) 
                     (b2 := a_SSigma psi0 b3 (close_tm_wrt_tm x b2)).
    exists_apply_MultiPar x.
    exists_apply_MultiPar x.
    exists_apply_GEq x.
  - (* SSigma Fst *)
    repeat invert_Joins.
    match goal with [H0 : MultiPar _ _ (a_SSigma _ _ _) _ |- _ ] => 
        eapply MultiPar_SSigma_inv in H0; try reflexivity;
        move: H0 => [A1' [B1' [? [? hh]]]]; subst; move: hh => [L1 h1] end.
    match goal with [H0 : MultiPar _ _ (a_SSigma _ _ _) _ |- _ ] => 
        eapply MultiPar_SSigma_inv in H0; try reflexivity;
        move: H0 => [A2' [B2' [? [? hh]]]]; subst; move: hh => [L2 h2] end.
    match goal with [H:GEq _ _ _ _ |- _ ] => inversion H end. subst.
    eapply join; eauto.
  - (* SSigma Snd *)
    repeat invert_Joins.
    match goal with [H0 : MultiPar _ _ (a_SSigma _ _ _) _ |- _ ] => 
        eapply MultiPar_SSigma_inv in H0; try reflexivity;
        move: H0 => [A1' [B1' [? [? hh]]]]; subst; move: hh => [L1 h1] end.
    match goal with [H0 : MultiPar _ _ (a_SSigma _ _ _) _ |- _ ] => 
        eapply MultiPar_SSigma_inv in H0; try reflexivity;
        move: H0 => [A2' [B2' [? [? hh]]]]; subst; move: hh => [L2 h2] end.
    match goal with [H:GEq _ _ _ _ |- _ ] => inversion H end. subst.
    pick fresh x. repeat spec x.
    rewrite (subst_tm_tm_intro x B1); eauto.
    rewrite (subst_tm_tm_intro x B2); eauto.
    eapply join.
    eapply MultiPar_subst3; try eassumption.
    eapply MultiPar_subst3; try eassumption.
    move: CEq_GEq_equality_substitution => [_ sub].
    eapply sub with (P2 := nil); simpl_env; eauto.
    eapply CEq_Leq; eauto. reflexivity.
  - (* SPair *)
    eapply Joins_SPair; eauto.
  - (* Proj1 *)
    eapply Joins_Proj1; eauto.
  - (* Proj2 *)
    eapply Joins_Proj2; eauto.
  - (* Sum Cong *)
    eapply Joins_Sum; eauto.
  - (* Sum Fst *)
    invert_Joins.
    eapply MultiPar_Sum_inv in H0; try reflexivity.
    move: H0 => [A1'1 [A2'1 hh]]. split_hyp. subst. 
    eapply MultiPar_Sum_inv in H1; try reflexivity.
    move: H1 => [A1'2 [A2'2 hh]]. split_hyp. subst. 
    match goal with [H:GEq _ _ _ _ |- _ ] => inversion H end. subst.
    eapply join; eauto.
  - (* Sum Snd *)
    invert_Joins.
    eapply MultiPar_Sum_inv in H0; try reflexivity.
    move: H0 => [A1'1 [A2'1 hh]]. split_hyp. subst. 
    eapply MultiPar_Sum_inv in H1; try reflexivity.
    move: H1 => [A1'2 [A2'2 hh]]. split_hyp. subst. 
    match goal with [H:GEq _ _ _ _ |- _ ] => inversion H end. subst.
    eapply join; eauto.
  - (* Inj1 *)
    eapply Joins_Inj1; eauto.
  - (* Inj2 *)
    eapply Joins_Inj2; eauto.
  - (* Case *)
    eapply Joins_Case; eauto.
  - eapply join; eauto.
  - eapply join; eauto.    
  - (* SubstIrrel *)
    pick fresh x. repeat spec x.
    invert_Joins.
    move: (GEq_uniq H3) => u. destruct_uniq.
    rewrite (subst_tm_tm_intro x); auto.
    rewrite (subst_tm_tm_intro x b2); auto.
    eapply join.
    instantiate (1 := (subst_tm_tm a1 x b0)).
    eapply MultiPar_subst3_CMultiPar; try eassumption.
    eapply CMP_Nleq; auto.
    instantiate (1 := (subst_tm_tm a1 x b3)).
    eapply MultiPar_subst3_CMultiPar; try eassumption.
    eapply CMP_Nleq; auto.
    eapply GEq_substitution_irrel with (P2 := nil); eauto.
Qed.

Lemma DefEq_Consistent : forall S D A B, DefEq S D A B -> Consistent A B.
Proof. 
  intros. 
  eapply Joins_Consistent.
  eapply DefEq_Joins.
  eauto.
Qed.
