(* -*- company-coq-initial-fold-state: bullets; -*- *)

Require Export Qual.metalib.
Require Export Qual.tactics.
Require Export Qual.labels. 
Require Export Qual.weakening.
Require Export Qual.subst.

Set Implicit Arguments.
Open Scope grade_scope.


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
    eapply Grade_open; eauto.
  - (* Beta / AppIrrel *)
    invert_Grade; subst.
    pick fresh x;  spec x.
    eapply Grade_open_irrel; eauto.
  - (* SPair *)
   invert_Grade; subst; eauto; try done.
  - (* LetPair *)
    invert_Grade; subst;
    pick fresh x; spec x.
    eapply G_AppRel; eauto using leq_Bot.
    eapply Grade_open; eauto.
    eapply G_AppRel; eauto using leq_Bot.
    eapply Grade_open_irrel; eauto. 
Qed.
