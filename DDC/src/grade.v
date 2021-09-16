(* -*- company-coq-initial-fold-state: bullets; -*- *)

Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels. 
Require Export Qual.weakening.
Require Export Qual.subst.

Set Implicit Arguments.
Open Scope grade_scope.

Ltac invert_CGrade a :=
  match goal with 
    [ H : CGrade ?P ?phi ?psi a |- _] => inversion H ; subst 
  end.

Lemma Step_Grade : forall a b,  Step a b -> forall P phi, Grade P phi a -> Grade P phi b.
Proof.
  intros a b S. induction S; intros.
  all: try match goal with 
      [ H : Grade ?P ?phi ?b |- _ ] => inversion H ; clear H; subst end.
  all: intros; eauto.
 
  all: try solve [invert_Grade; subst;
                  eauto using leq_join_r]. 
  - (* Beta / AppRel *)
    invert_Grade; subst.
    pick fresh x;  spec x.
    invert_CGrade b; auto.
    eapply Grade_open; eauto.
    eapply Grade_open_irrel; eauto.
  - (* SPair *)
   invert_Grade; invert_CGrade a1; subst; eauto; try done.
  - (* LetPair *)
    invert_Grade; subst;
    pick fresh x; spec x.
    eapply G_App; eauto using leq_Bot.
    invert_CGrade a1.
    eapply Grade_open; eauto.
    eapply Grade_open_irrel; eauto. 
Qed.

