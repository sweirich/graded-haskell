Require Import ssreflect.
Require Import Metalib.Metatheory.

(* look for other places to use this tactic *)
Ltac binds_mid_eq := 
  match goal with [ H : binds ?x ?psi (?P2 ++ ?a ++ ?P) |- _ ] => 
                      apply binds_mid_eq in H; subst; try solve_uniq; clear H end.

Lemma helper_uniq : forall {A} P2 x (psi0 psi1 : A) P1, uniq  (P2 ++ x ~ psi0 ++ P1) -> uniq (P2 ++ x ~ psi1 ++ P1). 
Proof. 
  intros. solve_uniq.
Qed. 

(* ------- these should be added to the metatheory library ------------------------- *)

(* If we have identified a variable in the middle of a uniq environment, 
   it fixes the front and back. *)
Lemma uniq_mid A x (a a':A) G1 : forall G2 G1' G2',
    uniq (G1 ++ (x ~ a) ++ G2) -> 
    (G1 ++ x ~ a ++ G2) = (G1' ++ x ~ a' ++ G2') ->
    G1 = G1' /\ a = a' /\ G2 = G2'.
Proof.    
  induction G1.
  + intros.
    destruct G1'; inversion H0; simpl_env in *. auto.
    subst. destruct_uniq. fsetdec.
  + intros.
    destruct a0 as [y b].
    simpl_env in *.
    destruct_uniq.
    have NE: not (y = x). fsetdec.
    destruct G1' as [|[z c]]. simpl_env in H0. inversion H0. done.
    inversion H0. subst.
    simpl_env in *.
    specialize (IHG1 G2 G1' G2').
    destruct IHG1 as [E1 [E2 E3]]; auto.
    subst. auto.
Qed.

(* If x is in an environment, it is either in the front half or 
   the back half. *)
Lemma binds_split A x (a:A) G : binds x a G -> exists G1 G2, G = G2 ++ [(x, a)] ++ G1.
Proof.
  move=>B. induction G.
  + inversion B.
  + destruct a0 as [y b].
    apply binds_cons_1 in B.
    destruct B as [[E1 E2]|E]. subst.
    ++ exists G. exists nil. auto.
    ++ destruct (IHG E) as [G1 [G2 E2]].
       subst.
       eexists. exists ((y ~ b) ++ G2). simpl_env. 
       eauto.
Qed.

(* If we divide up a context containing a variable, it either appears in the 
   front half or the back half *)
Lemma ctx_align_eq A G1 G2 (x:atom) (a:A) G0 G3 :
  uniq (G2 ++ x ~ a ++ G1) ->
  G2 ++ x ~ a ++ G1 = G0 ++ G3 ->
  (exists G0' G0'', G0 = G0' ++ x ~ a ++ G0'' /\ G2 = G0' /\ G1 = G0'' ++ G3) \/
  (exists G3' G3'', G3 = G3' ++ x ~ a ++ G3'' /\ G2 = G0 ++ G3' /\ G1 = G3''). 
Proof.
  intros U E.
  have B: binds x a (G0 ++ G3). { rewrite <- E. auto. }
  rewrite -> binds_app_iff in B.
  destruct B as [h1|h1]. 
  + left.
    destruct (binds_split _ _ _ _ h1) as [G0'' [G0' E2]].
    exists G0'. exists G0''. split. auto.
    subst.
    simpl_env in E.
    edestruct uniq_mid with (G1 := G2) (G1' := G0')
                            (G2 := G1) (G2' := G0'' ++ G3); eauto.
    tauto.
  + right.
    destruct (binds_split _ _ _ _ h1) as [G0'' [G0' E2]].
    exists G0'. exists G0''. split. auto.
    subst.
    edestruct uniq_mid with (G1 := G2) (G1' := G0 ++ G0')
                            (G2 := G1) (G2' := G0''); simpl_env; eauto.
    tauto.
Qed.
