(* Parameterization of the po-semiring *)

Require Import Metalib.Metatheory.

Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Sumbool.
Require Import Coq.Program.Equality.

Module Type UsageSig.

Parameter usage : Set. 
Parameter Irr : usage.
Parameter Lin : usage.
Parameter qeqb  : usage -> usage -> bool.
Parameter qleb  : usage -> usage -> bool.
Parameter qplus : usage -> usage -> usage.
Parameter qmul  : usage -> usage -> usage. 

(* Equality *)
Definition t := usage.
Definition eq := @Logic.eq usage.
Definition eqb  := qeqb.
Parameter q_eq_dec : forall (A : usage) (B : usage), { A = B } + { not (A = B) }.
Instance equ  : @EqDec_eq usage := q_eq_dec. 
Parameter eqb_eq : forall (n m : usage), qeqb n m = true <-> n = m.
Definition eq_equiv : Equivalence (@Logic.eq usage) := eq_equivalence.
Definition eq_dec := q_eq_dec.
Include BackportEq.

(* Size *)
Definition size_usage : usage -> nat := fun _ => 1%nat.
Lemma size_usage_min : forall q1, (1 <= size_usage q1). intros. unfold size_usage. auto. Qed.

(* Notation *)
Declare Scope usage_scope.
Bind Scope usage_scope with usage.
Local Open Scope usage_scope.

Infix "=?" := qeqb (at level 70) : usage_scope.
Infix "<=?" := qleb (at level 70) : usage_scope.
Notation "q1 <= q2" := (is_true (qleb q1 q2)) (at level 70)  : usage_scope.
Notation "0" := Irr : usage_scope.
Notation "1" := Lin : usage_scope.
Notation "x + y"  := (qplus x y) : usage_scope. 
Notation "x * y " := (qmul x y)  : usage_scope.

(* (Semi-)ring *)
Axiom qplus_0_l : forall x, 0 + x = x.
Axiom qmul_0_l : forall x, 0 * x = 0.
Axiom qplus_comm : forall (n m : usage), n + m = m + n.
Axiom qplus_assoc : forall (n m p : usage), n + (m + p) = (n + m) + p.
Axiom qmul_1_l : forall n, 1*n = n.
(*Axiom qmul_comm : forall n m, n*m = m*n. *)
Axiom qmul_assoc : forall n m p, n*(m*p) = (n*m)*p.
Axiom distr_l : forall n m p, (n + m)*p = n*p + m*p.

(* Cannot derive these if multiplication is not commutative *)
Axiom qmul_0_r : forall x, x * 0 = 0.
Axiom qmul_1_r : forall n, n*1 = n.
Axiom distr_r : forall n m p, p * (n + m) = p * n + p * m.

(* Partial order *)
Definition leb  := qleb.
Definition le n m := is_true (qleb n m).
Axiom leb_le : forall (n m : usage), (n <=? m) = true <-> n <= m.
Axiom qleb_refl : forall n, is_true (n <=? n).
Axiom qleb_trans: forall m n p, is_true (n <=? m) -> is_true (m <=? p) -> is_true (n <=? p).

Instance le_preorder : PreOrder le.
Proof. split. intro x. apply qleb_refl. unfold Transitive. intros. eapply qleb_trans; eauto. Qed.

Axiom po_semiring1 : forall a b c , a <= b -> a + c <= b + c.
Axiom po_semiring2 : forall a b c , a <= b -> a * c <= b * c.
Axiom po_semiring3 : forall a b c , a <= b -> c * a <= c * b.

End UsageSig.

Declare Module Usage : UsageSig.
Export Usage.





