Require Import Metalib.Metatheory. Require Export Metalib.LibLNgen. Require Export Qtt.usage_sig. 
(** syntax *)
Definition tmvar : Set := var. (*r variables *)
Definition qvar : Set := var.
Definition u : Set := usage.
Definition index : Set := nat. (*r indices *)

Inductive q : Set :=  (*r quantity, or usage expression *)
 | q_Var_b (_:nat)
 | q_Var_f (m:qvar)
 | q_Const (u5:u)
 | q_Plus (q1:q) (q2:q)
 | q_Mul (q1:q) (q2:q).

Inductive tm : Set :=  (*r terms and types *)
 | a_TyUnit : tm
 | a_TmUnit : tm
 | a_letunitB (a:tm) (b:tm) (B:tm)
 | a_Pi (q5:q) (A:tm) (B:tm)
 | a_Lam (q5:q) (A:tm) (a:tm)
 | a_App (a:tm) (b:tm)
 | a_Box (q5:q) (A:tm)
 | a_LetBoxB (a:tm) (b:tm) (B:tm)
 | a_Type : tm
 | a_Var_b (_:nat)
 | a_Var_f (x:tmvar)
 | a_box (q5:q) (a:tm)
 | a_Let (a:tm) (b:tm)
 | a_Sum (A1:tm) (A2:tm)
 | a_Inj1 (a:tm)
 | a_Inj2 (a:tm)
 | a_Case (q5:q) (a:tm) (b1:tm) (b2:tm) (B:tm)
 | a_Sigma (q5:q) (A:tm) (B:tm)
 | a_Tensor (a:tm) (b:tm)
 | a_Spread (a:tm) (b:tm) (B:tm)
 | a_AllU (A:tm)
 | a_LamU (a:tm)
 | a_AppU (a:tm) (q5:q).

Inductive sort : Set :=  (*r binding classifier *)
 | Tm (A:tm).

Definition context : Set := list ( atom * (q * sort ) ).

Definition D : Set := list ( atom * sort ).

Definition heap : Set := list ( atom * ( q * (context * tm * tm )) ).

Definition supp : Type := atoms.

Definition qlist : Set := list q.

Definition n : Set := nat.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_q_wrt_q_rec (k:nat) (r5:q) (r_6:q) {struct r_6}: q :=
  match r_6 with
  | (q_Var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => q_Var_b nat
        | inleft (right _) => r5
        | inright _ => q_Var_b (nat - 1)
      end
  | (q_Var_f m) => q_Var_f m
  | (q_Const u5) => q_Const u5
  | (q_Plus q1 q2) => q_Plus (open_q_wrt_q_rec k r5 q1) (open_q_wrt_q_rec k r5 q2)
  | (q_Mul q1 q2) => q_Mul (open_q_wrt_q_rec k r5 q1) (open_q_wrt_q_rec k r5 q2)
end.

Fixpoint open_tm_wrt_tm_rec (k:nat) (a5:tm) (a_6:tm) {struct a_6}: tm :=
  match a_6 with
  | a_TyUnit => a_TyUnit 
  | a_TmUnit => a_TmUnit 
  | (a_letunitB a b B) => a_letunitB (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b) (open_tm_wrt_tm_rec k a5 B)
  | (a_Pi q5 A B) => a_Pi q5 (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_Lam q5 A a) => a_Lam q5 (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 a)
  | (a_App a b) => a_App (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b)
  | (a_Box q5 A) => a_Box q5 (open_tm_wrt_tm_rec k a5 A)
  | (a_LetBoxB a b B) => a_LetBoxB (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec (S k) a5 b) (open_tm_wrt_tm_rec k a5 B)
  | a_Type => a_Type 
  | (a_Var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => a_Var_b nat
        | inleft (right _) => a5
        | inright _ => a_Var_b (nat - 1)
      end
  | (a_Var_f x) => a_Var_f x
  | (a_box q5 a) => a_box q5 (open_tm_wrt_tm_rec k a5 a)
  | (a_Let a b) => a_Let (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_Sum A1 A2) => a_Sum (open_tm_wrt_tm_rec k a5 A1) (open_tm_wrt_tm_rec k a5 A2)
  | (a_Inj1 a) => a_Inj1 (open_tm_wrt_tm_rec k a5 a)
  | (a_Inj2 a) => a_Inj2 (open_tm_wrt_tm_rec k a5 a)
  | (a_Case q5 a b1 b2 B) => a_Case q5 (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b1) (open_tm_wrt_tm_rec k a5 b2) (open_tm_wrt_tm_rec k a5 B)
  | (a_Sigma q5 A B) => a_Sigma q5 (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_Tensor a b) => a_Tensor (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b)
  | (a_Spread a b B) => a_Spread (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec (S k) a5 b) (open_tm_wrt_tm_rec k a5 B)
  | (a_AllU A) => a_AllU (open_tm_wrt_tm_rec k a5 A)
  | (a_LamU a) => a_LamU (open_tm_wrt_tm_rec k a5 a)
  | (a_AppU a q5) => a_AppU (open_tm_wrt_tm_rec k a5 a) q5
end.

Fixpoint open_tm_wrt_q_rec (k:nat) (r5:q) (a5:tm) {struct a5}: tm :=
  match a5 with
  | a_TyUnit => a_TyUnit 
  | a_TmUnit => a_TmUnit 
  | (a_letunitB a b B) => a_letunitB (open_tm_wrt_q_rec k r5 a) (open_tm_wrt_q_rec k r5 b) (open_tm_wrt_q_rec k r5 B)
  | (a_Pi q5 A B) => a_Pi (open_q_wrt_q_rec k r5 q5) (open_tm_wrt_q_rec k r5 A) (open_tm_wrt_q_rec k r5 B)
  | (a_Lam q5 A a) => a_Lam (open_q_wrt_q_rec k r5 q5) (open_tm_wrt_q_rec k r5 A) (open_tm_wrt_q_rec k r5 a)
  | (a_App a b) => a_App (open_tm_wrt_q_rec k r5 a) (open_tm_wrt_q_rec k r5 b)
  | (a_Box q5 A) => a_Box (open_q_wrt_q_rec k r5 q5) (open_tm_wrt_q_rec k r5 A)
  | (a_LetBoxB a b B) => a_LetBoxB (open_tm_wrt_q_rec k r5 a) (open_tm_wrt_q_rec k r5 b) (open_tm_wrt_q_rec k r5 B)
  | a_Type => a_Type 
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_box q5 a) => a_box (open_q_wrt_q_rec k r5 q5) (open_tm_wrt_q_rec k r5 a)
  | (a_Let a b) => a_Let (open_tm_wrt_q_rec k r5 a) (open_tm_wrt_q_rec k r5 b)
  | (a_Sum A1 A2) => a_Sum (open_tm_wrt_q_rec k r5 A1) (open_tm_wrt_q_rec k r5 A2)
  | (a_Inj1 a) => a_Inj1 (open_tm_wrt_q_rec k r5 a)
  | (a_Inj2 a) => a_Inj2 (open_tm_wrt_q_rec k r5 a)
  | (a_Case q5 a b1 b2 B) => a_Case (open_q_wrt_q_rec k r5 q5) (open_tm_wrt_q_rec k r5 a) (open_tm_wrt_q_rec k r5 b1) (open_tm_wrt_q_rec k r5 b2) (open_tm_wrt_q_rec k r5 B)
  | (a_Sigma q5 A B) => a_Sigma (open_q_wrt_q_rec k r5 q5) (open_tm_wrt_q_rec k r5 A) (open_tm_wrt_q_rec k r5 B)
  | (a_Tensor a b) => a_Tensor (open_tm_wrt_q_rec k r5 a) (open_tm_wrt_q_rec k r5 b)
  | (a_Spread a b B) => a_Spread (open_tm_wrt_q_rec k r5 a) (open_tm_wrt_q_rec k r5 b) (open_tm_wrt_q_rec k r5 B)
  | (a_AllU A) => a_AllU (open_tm_wrt_q_rec (S k) r5 A)
  | (a_LamU a) => a_LamU (open_tm_wrt_q_rec (S k) r5 a)
  | (a_AppU a q5) => a_AppU (open_tm_wrt_q_rec k r5 a) (open_q_wrt_q_rec k r5 q5)
end.

Definition open_sort_wrt_tm_rec (k:nat) (a5:tm) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (open_tm_wrt_tm_rec k a5 A)
end.

Definition open_sort_wrt_q_rec (k:nat) (r5:q) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (open_tm_wrt_q_rec k r5 A)
end.

Definition open_sort_wrt_tm a5 sort5 := open_sort_wrt_tm_rec 0 sort5 a5.

Definition open_tm_wrt_q r5 a5 := open_tm_wrt_q_rec 0 a5 r5.

Definition open_sort_wrt_q r5 sort5 := open_sort_wrt_q_rec 0 sort5 r5.

Definition open_tm_wrt_tm a5 a_6 := open_tm_wrt_tm_rec 0 a_6 a5.

Definition open_q_wrt_q r5 r_6 := open_q_wrt_q_rec 0 r_6 r5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_q *)
Inductive lc_q : q -> Prop :=    (* defn lc_q *)
 | lc_q_Var_f : forall (m:qvar),
     (lc_q (q_Var_f m))
 | lc_q_Const : forall (u5:u),
     (lc_q (q_Const u5))
 | lc_q_Plus : forall (q1 q2:q),
     (lc_q q1) ->
     (lc_q q2) ->
     (lc_q (q_Plus q1 q2))
 | lc_q_Mul : forall (q1 q2:q),
     (lc_q q1) ->
     (lc_q q2) ->
     (lc_q (q_Mul q1 q2)).

(* defns LC_tm *)
Inductive lc_tm : tm -> Prop :=    (* defn lc_tm *)
 | lc_a_TyUnit : 
     (lc_tm a_TyUnit)
 | lc_a_TmUnit : 
     (lc_tm a_TmUnit)
 | lc_a_letunitB : forall (a b B:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm B) ->
     (lc_tm (a_letunitB a b B))
 | lc_a_Pi : forall (q5:q) (A B:tm),
     (lc_q q5) ->
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Pi q5 A B))
 | lc_a_Lam : forall (q5:q) (A a:tm),
     (lc_q q5) ->
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     (lc_tm (a_Lam q5 A a))
 | lc_a_App : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_App a b))
 | lc_a_Box : forall (q5:q) (A:tm),
     (lc_q q5) ->
     (lc_tm A) ->
     (lc_tm (a_Box q5 A))
 | lc_a_LetBoxB : forall (a b B:tm),
     (lc_tm a) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm B) ->
     (lc_tm (a_LetBoxB a b B))
 | lc_a_Type : 
     (lc_tm a_Type)
 | lc_a_Var_f : forall (x:tmvar),
     (lc_tm (a_Var_f x))
 | lc_a_box : forall (q5:q) (a:tm),
     (lc_q q5) ->
     (lc_tm a) ->
     (lc_tm (a_box q5 a))
 | lc_a_Let : forall (a b:tm),
     (lc_tm a) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm (a_Let a b))
 | lc_a_Sum : forall (A1 A2:tm),
     (lc_tm A1) ->
     (lc_tm A2) ->
     (lc_tm (a_Sum A1 A2))
 | lc_a_Inj1 : forall (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Inj1 a))
 | lc_a_Inj2 : forall (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Inj2 a))
 | lc_a_Case : forall (q5:q) (a b1 b2 B:tm),
     (lc_q q5) ->
     (lc_tm a) ->
     (lc_tm b1) ->
     (lc_tm b2) ->
     (lc_tm B) ->
     (lc_tm (a_Case q5 a b1 b2 B))
 | lc_a_Sigma : forall (q5:q) (A B:tm),
     (lc_q q5) ->
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Sigma q5 A B))
 | lc_a_Tensor : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_Tensor a b))
 | lc_a_Spread : forall (a b B:tm),
     (lc_tm a) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm B) ->
     (lc_tm (a_Spread a b B))
 | lc_a_AllU : forall (A:tm),
      ( forall m , lc_tm  ( open_tm_wrt_q A (q_Var_f m) )  )  ->
     (lc_tm (a_AllU A))
 | lc_a_LamU : forall (a:tm),
      ( forall m , lc_tm  ( open_tm_wrt_q a (q_Var_f m) )  )  ->
     (lc_tm (a_LamU a))
 | lc_a_AppU : forall (a:tm) (q5:q),
     (lc_tm a) ->
     (lc_q q5) ->
     (lc_tm (a_AppU a q5)).

(* defns LC_sort *)
Inductive lc_sort : sort -> Prop :=    (* defn lc_sort *)
 | lc_Tm : forall (A:tm),
     (lc_tm A) ->
     (lc_sort (Tm A)).
(** free variables *)
Fixpoint fv_q_q (r5:q) : vars :=
  match r5 with
  | (q_Var_b nat) => {}
  | (q_Var_f m) => {{m}}
  | (q_Const u5) => {}
  | (q_Plus q1 q2) => (fv_q_q q1) \u (fv_q_q q2)
  | (q_Mul q1 q2) => (fv_q_q q1) \u (fv_q_q q2)
end.

Fixpoint fv_tm_tm (a5:tm) : vars :=
  match a5 with
  | a_TyUnit => {}
  | a_TmUnit => {}
  | (a_letunitB a b B) => (fv_tm_tm a) \u (fv_tm_tm b) \u (fv_tm_tm B)
  | (a_Pi q5 A B) => (fv_tm_tm A) \u (fv_tm_tm B)
  | (a_Lam q5 A a) => (fv_tm_tm A) \u (fv_tm_tm a)
  | (a_App a b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_Box q5 A) => (fv_tm_tm A)
  | (a_LetBoxB a b B) => (fv_tm_tm a) \u (fv_tm_tm b) \u (fv_tm_tm B)
  | a_Type => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {{x}}
  | (a_box q5 a) => (fv_tm_tm a)
  | (a_Let a b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_Sum A1 A2) => (fv_tm_tm A1) \u (fv_tm_tm A2)
  | (a_Inj1 a) => (fv_tm_tm a)
  | (a_Inj2 a) => (fv_tm_tm a)
  | (a_Case q5 a b1 b2 B) => (fv_tm_tm a) \u (fv_tm_tm b1) \u (fv_tm_tm b2) \u (fv_tm_tm B)
  | (a_Sigma q5 A B) => (fv_tm_tm A) \u (fv_tm_tm B)
  | (a_Tensor a b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_Spread a b B) => (fv_tm_tm a) \u (fv_tm_tm b) \u (fv_tm_tm B)
  | (a_AllU A) => (fv_tm_tm A)
  | (a_LamU a) => (fv_tm_tm a)
  | (a_AppU a q5) => (fv_tm_tm a)
end.

Fixpoint fv_q_tm (a5:tm) : vars :=
  match a5 with
  | a_TyUnit => {}
  | a_TmUnit => {}
  | (a_letunitB a b B) => (fv_q_tm a) \u (fv_q_tm b) \u (fv_q_tm B)
  | (a_Pi q5 A B) => (fv_q_q q5) \u (fv_q_tm A) \u (fv_q_tm B)
  | (a_Lam q5 A a) => (fv_q_q q5) \u (fv_q_tm A) \u (fv_q_tm a)
  | (a_App a b) => (fv_q_tm a) \u (fv_q_tm b)
  | (a_Box q5 A) => (fv_q_q q5) \u (fv_q_tm A)
  | (a_LetBoxB a b B) => (fv_q_tm a) \u (fv_q_tm b) \u (fv_q_tm B)
  | a_Type => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {}
  | (a_box q5 a) => (fv_q_q q5) \u (fv_q_tm a)
  | (a_Let a b) => (fv_q_tm a) \u (fv_q_tm b)
  | (a_Sum A1 A2) => (fv_q_tm A1) \u (fv_q_tm A2)
  | (a_Inj1 a) => (fv_q_tm a)
  | (a_Inj2 a) => (fv_q_tm a)
  | (a_Case q5 a b1 b2 B) => (fv_q_q q5) \u (fv_q_tm a) \u (fv_q_tm b1) \u (fv_q_tm b2) \u (fv_q_tm B)
  | (a_Sigma q5 A B) => (fv_q_q q5) \u (fv_q_tm A) \u (fv_q_tm B)
  | (a_Tensor a b) => (fv_q_tm a) \u (fv_q_tm b)
  | (a_Spread a b B) => (fv_q_tm a) \u (fv_q_tm b) \u (fv_q_tm B)
  | (a_AllU A) => (fv_q_tm A)
  | (a_LamU a) => (fv_q_tm a)
  | (a_AppU a q5) => (fv_q_tm a) \u (fv_q_q q5)
end.

Definition fv_tm_sort (sort5:sort) : vars :=
  match sort5 with
  | (Tm A) => (fv_tm_tm A)
end.

Definition fv_q_sort (sort5:sort) : vars :=
  match sort5 with
  | (Tm A) => (fv_q_tm A)
end.

(** substitutions *)
Fixpoint subst_q_q (r5:q) (m5:qvar) (r_6:q) {struct r_6} : q :=
  match r_6 with
  | (q_Var_b nat) => q_Var_b nat
  | (q_Var_f m) => (if eq_var m m5 then r5 else (q_Var_f m))
  | (q_Const u5) => q_Const u5
  | (q_Plus q1 q2) => q_Plus (subst_q_q r5 m5 q1) (subst_q_q r5 m5 q2)
  | (q_Mul q1 q2) => q_Mul (subst_q_q r5 m5 q1) (subst_q_q r5 m5 q2)
end.

Fixpoint subst_tm_tm (a5:tm) (x5:tmvar) (a_6:tm) {struct a_6} : tm :=
  match a_6 with
  | a_TyUnit => a_TyUnit 
  | a_TmUnit => a_TmUnit 
  | (a_letunitB a b B) => a_letunitB (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b) (subst_tm_tm a5 x5 B)
  | (a_Pi q5 A B) => a_Pi q5 (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 B)
  | (a_Lam q5 A a) => a_Lam q5 (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 a)
  | (a_App a b) => a_App (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b)
  | (a_Box q5 A) => a_Box q5 (subst_tm_tm a5 x5 A)
  | (a_LetBoxB a b B) => a_LetBoxB (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b) (subst_tm_tm a5 x5 B)
  | a_Type => a_Type 
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => (if eq_var x x5 then a5 else (a_Var_f x))
  | (a_box q5 a) => a_box q5 (subst_tm_tm a5 x5 a)
  | (a_Let a b) => a_Let (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b)
  | (a_Sum A1 A2) => a_Sum (subst_tm_tm a5 x5 A1) (subst_tm_tm a5 x5 A2)
  | (a_Inj1 a) => a_Inj1 (subst_tm_tm a5 x5 a)
  | (a_Inj2 a) => a_Inj2 (subst_tm_tm a5 x5 a)
  | (a_Case q5 a b1 b2 B) => a_Case q5 (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b1) (subst_tm_tm a5 x5 b2) (subst_tm_tm a5 x5 B)
  | (a_Sigma q5 A B) => a_Sigma q5 (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 B)
  | (a_Tensor a b) => a_Tensor (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b)
  | (a_Spread a b B) => a_Spread (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b) (subst_tm_tm a5 x5 B)
  | (a_AllU A) => a_AllU (subst_tm_tm a5 x5 A)
  | (a_LamU a) => a_LamU (subst_tm_tm a5 x5 a)
  | (a_AppU a q5) => a_AppU (subst_tm_tm a5 x5 a) q5
end.

Fixpoint subst_q_tm (r5:q) (m5:qvar) (a5:tm) {struct a5} : tm :=
  match a5 with
  | a_TyUnit => a_TyUnit 
  | a_TmUnit => a_TmUnit 
  | (a_letunitB a b B) => a_letunitB (subst_q_tm r5 m5 a) (subst_q_tm r5 m5 b) (subst_q_tm r5 m5 B)
  | (a_Pi q5 A B) => a_Pi (subst_q_q r5 m5 q5) (subst_q_tm r5 m5 A) (subst_q_tm r5 m5 B)
  | (a_Lam q5 A a) => a_Lam (subst_q_q r5 m5 q5) (subst_q_tm r5 m5 A) (subst_q_tm r5 m5 a)
  | (a_App a b) => a_App (subst_q_tm r5 m5 a) (subst_q_tm r5 m5 b)
  | (a_Box q5 A) => a_Box (subst_q_q r5 m5 q5) (subst_q_tm r5 m5 A)
  | (a_LetBoxB a b B) => a_LetBoxB (subst_q_tm r5 m5 a) (subst_q_tm r5 m5 b) (subst_q_tm r5 m5 B)
  | a_Type => a_Type 
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_box q5 a) => a_box (subst_q_q r5 m5 q5) (subst_q_tm r5 m5 a)
  | (a_Let a b) => a_Let (subst_q_tm r5 m5 a) (subst_q_tm r5 m5 b)
  | (a_Sum A1 A2) => a_Sum (subst_q_tm r5 m5 A1) (subst_q_tm r5 m5 A2)
  | (a_Inj1 a) => a_Inj1 (subst_q_tm r5 m5 a)
  | (a_Inj2 a) => a_Inj2 (subst_q_tm r5 m5 a)
  | (a_Case q5 a b1 b2 B) => a_Case (subst_q_q r5 m5 q5) (subst_q_tm r5 m5 a) (subst_q_tm r5 m5 b1) (subst_q_tm r5 m5 b2) (subst_q_tm r5 m5 B)
  | (a_Sigma q5 A B) => a_Sigma (subst_q_q r5 m5 q5) (subst_q_tm r5 m5 A) (subst_q_tm r5 m5 B)
  | (a_Tensor a b) => a_Tensor (subst_q_tm r5 m5 a) (subst_q_tm r5 m5 b)
  | (a_Spread a b B) => a_Spread (subst_q_tm r5 m5 a) (subst_q_tm r5 m5 b) (subst_q_tm r5 m5 B)
  | (a_AllU A) => a_AllU (subst_q_tm r5 m5 A)
  | (a_LamU a) => a_LamU (subst_q_tm r5 m5 a)
  | (a_AppU a q5) => a_AppU (subst_q_tm r5 m5 a) (subst_q_q r5 m5 q5)
end.

Definition subst_tm_sort (a5:tm) (x5:tmvar) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (subst_tm_tm a5 x5 A)
end.

Definition subst_q_sort (r5:q) (m5:qvar) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (subst_q_tm r5 m5 A)
end.



(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Parameter Beta : tm -> tm -> Prop.

Local Open Scope usage_scope.

(* *********************************************************************** *)
(** * Close *)

Fixpoint close_tm_wrt_tm_rec (n1 : nat) (x1 : tmvar) (a1 : tm) {struct a1} : tm :=
  match a1 with
    | a_TyUnit => a_TyUnit
    | a_TmUnit => a_TmUnit
    | a_letunitB a2 b1 B1 => a_letunitB (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_Pi q1 A1 B1 => a_Pi q1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_Lam q1 A1 a2 => a_Lam q1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 a2)
    | a_App a2 b1 => a_App (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Box q1 A1 => a_Box q1 (close_tm_wrt_tm_rec n1 x1 A1)
    | a_LetBoxB a2 b1 B1 => a_LetBoxB (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec (S n1) x1 b1) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_Type => a_Type
    | a_Var_f x2 => if (x1 == x2) then (a_Var_b n1) else (a_Var_f x2)
    | a_Var_b n2 => if (lt_ge_dec n2 n1) then (a_Var_b n2) else (a_Var_b (S n2))
    | a_box q1 a2 => a_box q1 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Let a2 b1 => a_Let (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec (S n1) x1 b1)
    | a_Sum A1 A2 => a_Sum (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec n1 x1 A2)
    | a_Inj1 a2 => a_Inj1 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Inj2 a2 => a_Inj2 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Case q1 a2 b1 b2 B1 => a_Case q1 (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1) (close_tm_wrt_tm_rec n1 x1 b2) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_Sigma q1 A1 B1 => a_Sigma q1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_Tensor a2 b1 => a_Tensor (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Spread a2 b1 B1 => a_Spread (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec (S n1) x1 b1) (close_tm_wrt_tm_rec n1 x1 B1)
    | a_AllU A => a_AllU (close_tm_wrt_tm_rec (S n1) x1 A)
    | a_LamU a => a_LamU (close_tm_wrt_tm_rec (S n1) x1 a)
    | a_AppU a u => a_AppU (close_tm_wrt_tm_rec n1 x1 a) u
  end.

Definition close_tm_wrt_tm x1 a1 := close_tm_wrt_tm_rec 0 x1 a1.

Definition sort_mul {A} (q1: q) (s : q * A) : q * A :=
  match s with 
  | (q2 , A) => (q_Mul q1 q2, A)
  end.

Definition ctx_mul {A} (q1 : q) (G : list (var * (q * A))) := 
  map (sort_mul q1) G.

Fixpoint ctx_plus {A} (G1 G2 : list (var * (q * A))) : list (var * (q * A)) :=
  match G1, G2 with 
  | nil , nil => nil
  | cons (x , (q1 , A)) G1' , cons (_, (q2, _)) G2' => cons (x, (q_Plus q1 q2, A)) (ctx_plus G1' G2')
  | _ , _ => nil
  end.


Inductive ctx {A} : list (atom * A) -> list (atom * (q * A)) -> Prop :=  
 | ctx_nil : 
     ctx nil nil 
 | ctx_cons : forall D (x:atom) G (q1:q) a,
     ctx D G ->
      ~ AtomSetImpl.In x (dom  D)  ->
     ctx (x ~ a ++ D ) (x ~ (q1,a) ++ G).

Arguments sort_mul {_}.
Arguments ctx_mul {_}.
Arguments ctx_plus {_}.
Arguments ctx {_}.

Hint Constructors ctx : core.



(** definitions *)

(* defns JOp *)
Inductive Step : tm -> tm -> Prop :=    (* defn Step *)
 | S_AppCong : forall (a b a':tm),
     lc_tm b ->
     Step a a' ->
     Step (a_App a b) (a_App a' b)
 | S_Beta : forall (q5:q) (A a b:tm),
     lc_q q5 ->
     lc_tm A ->
     lc_tm (a_Lam q5 A a) ->
     lc_tm b ->
     Step (a_App  ( (a_Lam q5 A a) )  b)  (open_tm_wrt_tm  a   b ) 
 | S_UnitCong : forall (a b B a':tm),
     lc_tm b ->
     lc_tm B ->
     Step a a' ->
     Step (a_letunitB a b B) (a_letunitB a' b B)
 | S_UnitBeta : forall (b B:tm),
     lc_tm B ->
     lc_tm b ->
     Step (a_letunitB a_TmUnit b B) b
 | S_BoxCong : forall (a b B a':tm),
     lc_tm (a_LetBoxB a b B) ->
     lc_tm B ->
     Step a a' ->
     Step (a_LetBoxB a b B) (a_LetBoxB a' b B)
 | S_BoxBeta : forall (q5:q) (a b B:tm),
     lc_q q5 ->
     lc_tm (a_LetBoxB (a_box q5 a) b B) ->
     lc_tm B ->
     lc_tm a ->
     Step (a_LetBoxB (a_box q5 a) b B)  (open_tm_wrt_tm  b   a ) 
 | S_CaseCong : forall (q5:q) (a b1 b2 B a':tm),
     lc_q q5 ->
     lc_tm b1 ->
     lc_tm b2 ->
     lc_tm B ->
     Step a a' ->
     Step (a_Case q5 a b1 b2 B) (a_Case q5 a' b1 b2 B)
 | S_Case1Beta : forall (q5:q) (a b1 b2 B:tm),
     lc_q q5 ->
     lc_tm b2 ->
     lc_tm B ->
     lc_tm b1 ->
     lc_tm a ->
     Step (a_Case q5  ( (a_Inj1 a) )  b1 b2 B) (a_App b1 a)
 | S_Case2Beta : forall (q5:q) (a b1 b2 B:tm),
     lc_q q5 ->
     lc_tm b1 ->
     lc_tm B ->
     lc_tm b2 ->
     lc_tm a ->
     Step (a_Case q5  ( (a_Inj2 a) )  b1 b2 B) (a_App b2 a)
 | S_SpreadCong : forall (a b B a':tm),
     lc_tm (a_Spread a b B) ->
     lc_tm B ->
     Step a a' ->
     Step (a_Spread a b B) (a_Spread a' b B)
 | S_SpreadBeta : forall (a0 a1 b B:tm),
     lc_tm (a_Spread (a_Tensor a0 a1) b B) ->
     lc_tm B ->
     lc_tm a0 ->
     lc_tm a1 ->
     Step (a_Spread (a_Tensor a0 a1) b B) (a_App  (open_tm_wrt_tm  b   a0 )  a1).

(* defns JSub *)
Inductive q_sub : q -> q -> Prop :=    (* defn q_sub *)
 | Const : forall (u1 u2:u),
      ( u1  <=  u2 )  ->
     q_sub (q_Const u1) (q_Const u2)
with ctx_sub : D -> context -> context -> Prop :=    (* defn ctx_sub *)
 | CS_Empty : 
     ctx_sub  nil   nil   nil 
 | CS_ConsTm : forall (D5:D) (x:tmvar) (A:tm) (G1:context) (q1:q) (G2:context) (q2:q),
     lc_tm A ->
     q_sub q1 q2 ->
     ctx_sub D5 G1 G2 ->
      ~ AtomSetImpl.In  x  (dom  D5 )  ->
     ctx_sub  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( q1 ,Tm  A ))  ++ G1 )   (  ( x ~( q2 ,Tm  A ))  ++ G2 ) .

(* defns JTyping *)
Inductive Typing : D -> context -> tm -> tm -> Prop :=    (* defn Typing *)
 | T_sub : forall (D5:D) (G2:context) (a A:tm) (G1:context),
     Typing D5 G1 a A ->
     ctx_sub D5 G1 G2 ->
     Typing D5 G2 a A
 | T_type : 
     Typing  nil   nil  a_Type a_Type
 | T_var : forall (D5:D) (x:tmvar) (A:tm) (G:context),
      ~ AtomSetImpl.In  x  (dom  D5 )  ->
     Typing D5 G A a_Type ->
     Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~(  (q_Const 1)  ,Tm  A ))  ++   (ctx_mul   (q_Const 0)    G )   )  (a_Var_f x) A
 | T_weak : forall (D5:D) (x:tmvar) (A:tm) (G1:context) (a B:tm) (G2:context),
      ~ AtomSetImpl.In  x  (dom  D5 )  ->
     Typing D5 G1 a B ->
     Typing D5 G2 A a_Type ->
     Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~(  (q_Const 0)  ,Tm  A ))  ++ G1 )  a B
 | T_pi : forall (L:vars) (D5:D) (G1 G2:context) (q5:q) (A B:tm) (r:q),
     lc_q q5 ->
     Typing D5 G1 A a_Type ->
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( r ,Tm  A ))  ++ G2 )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing D5  (ctx_plus  G1   G2 )  (a_Pi q5 A B) a_Type
 | T_lam : forall (L:vars) (D5:D) (G1:context) (q5:q) (A a B:tm) (G2:context),
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( q5 ,Tm  A ))  ++ G1 )   ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     Typing D5 G2 A a_Type ->
     Typing D5 G1 (a_Lam q5 A a) (a_Pi q5 A B)
 | T_app : forall (D5:D) (G1:context) (q5:q) (G2:context) (a b B A:tm),
     Typing D5 G1 a (a_Pi q5 A B) ->
     Typing D5 G2 b A ->
     Typing D5  (ctx_plus  G1     (ctx_mul  q5   G2 )   )  (a_App a b)  (open_tm_wrt_tm  B   b ) 
 | T_conv : forall (D5:D) (G1:context) (a B A:tm) (G2:context),
     Typing D5 G1 a A ->
     Typing D5 G2 B a_Type ->
      Beta  A   B  ->
     Typing D5 G1 a B
 | T_unit : 
     Typing  nil   nil  a_TmUnit a_TyUnit
 | T_Unit : 
     Typing  nil   nil  a_TyUnit a_Type
 | T_UnitE : forall (L:vars) (D5:D) (G1 G2:context) (a b:tm) (r:q) (B B1:tm) (G3:context),
     Typing D5 G1 a a_TyUnit ->
      B1 =  (open_tm_wrt_tm  B   a_TmUnit )   ->
     Typing D5 G2 b B1 ->
      ( forall y , y \notin  L  -> Typing  (  ( y  ~ Tm a_TyUnit )  ++ D5 )   (  ( y ~( r ,Tm  a_TyUnit ))  ++ G3 )   ( open_tm_wrt_tm B (a_Var_f y) )  a_Type )  ->
     Typing D5  (ctx_plus  G1   G2 )  (a_letunitB a b  ( (a_Lam r a_TyUnit B) ) )  (open_tm_wrt_tm  B   a ) 
 | T_Box : forall (D5:D) (G:context) (q5:q) (A:tm),
     lc_q q5 ->
     Typing D5 G A a_Type ->
     Typing D5 G (a_Box q5 A) a_Type
 | T_box : forall (D5:D) (q5:q) (G:context) (a A:tm),
     lc_q q5 ->
     Typing D5 G a A ->
     Typing D5  (ctx_mul  q5   G )  (a_box q5 a) (a_Box q5 A)
 | T_letbox : forall (L:vars) (D5:D) (G1 G2:context) (a b:tm) (r q5:q) (A B:tm) (G3:context),
     Typing D5 G1 a (a_Box q5 A) ->
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( q5 ,Tm  A ))  ++ G2 )   ( open_tm_wrt_tm b (a_Var_f x) )   (open_tm_wrt_tm  B   (a_box q5 (a_Var_f x)) )  )  ->
      ( forall y , y \notin  L  -> Typing  (  ( y  ~ Tm (a_Box q5 A) )  ++ D5 )   (  ( y ~( r ,Tm  (a_Box q5 A) ))  ++ G3 )   ( open_tm_wrt_tm B (a_Var_f y) )  a_Type )  ->
     Typing D5  (ctx_plus  G1   G2 )  (a_LetBoxB a b  ( (a_Lam r (a_Box q5 A) B) ) )  (open_tm_wrt_tm  B   a ) 
 | T_sum : forall (D5:D) (G1 G2:context) (A1 A2:tm),
     Typing D5 G1 A1 a_Type ->
     Typing D5 G2 A2 a_Type ->
     Typing D5  (ctx_plus  G1   G2 )  (a_Sum A1 A2) a_Type
 | T_inj1 : forall (D5:D) (G:context) (a A1 A2:tm) (G1:context),
     Typing D5 G a A1 ->
     Typing D5 G1 A2 a_Type ->
     Typing D5 G (a_Inj1 a) (a_Sum A1 A2)
 | T_inj2 : forall (D5:D) (G:context) (a A1 A2:tm) (G1:context),
     Typing D5 G a A2 ->
     Typing D5 G1 A1 a_Type ->
     Typing D5 G (a_Inj2 a) (a_Sum A1 A2)
 | T_case : forall (L:vars) (D5:D) (q5:q) (G1 G2:context) (a b1 b2:tm) (r:q) (A1 A2 B B1 B2:tm) (G3:context),
     q_sub  (q_Const 1)  q5 ->
     Typing D5 G1 a (a_Sum A1 A2) ->
      ( forall x , x \notin  L  ->   ( open_tm_wrt_tm B1 (a_Var_f x) )  =   (open_tm_wrt_tm  B   (a_Inj1 (a_Var_f x)) )    )  ->
      ( forall x , x \notin  L  ->   ( open_tm_wrt_tm B2 (a_Var_f x) )  =   (open_tm_wrt_tm  B   (a_Inj2 (a_Var_f x)) )    )  ->
     Typing D5 G2 b1 (a_Pi q5 A1 B1) ->
     Typing D5 G2 b2 (a_Pi q5 A2 B2) ->
      ( forall y , y \notin  L  -> Typing  (  ( y  ~ Tm (a_Sum A1 A2) )  ++ D5 )   (  ( y ~( r ,Tm  (a_Sum A1 A2) ))  ++ G3 )   ( open_tm_wrt_tm B (a_Var_f y) )  a_Type )  ->
     Typing D5  (ctx_plus    (ctx_mul  q5   G1 )     G2 )  (a_Case q5 a b1 b2  ( (a_Lam r (a_Sum A1 A2) B) ) )  (open_tm_wrt_tm  B   a ) 
 | T_Sigma : forall (L:vars) (D5:D) (G1 G2:context) (q5:q) (A B:tm) (r:q),
     lc_q q5 ->
     Typing D5 G1 A a_Type ->
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( r ,Tm  A ))  ++ G2 )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing D5  (ctx_plus  G1   G2 )  (a_Sigma q5 A B) a_Type
 | T_Tensor : forall (L:vars) (D5:D) (q5:q) (G1 G2:context) (a b A B:tm) (G3:context) (r:q),
     lc_q q5 ->
     Typing D5 G1 a A ->
     Typing D5 G2 b  (open_tm_wrt_tm  B   a )  ->
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( r ,Tm  A ))  ++ G3 )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing D5  (ctx_plus    (ctx_mul  q5   G1 )     G2 )  (a_Tensor a b) (a_Sigma q5 A B).


(** infrastructure *)
Hint Constructors Step q_sub ctx_sub Typing lc_q lc_tm lc_sort : core.


