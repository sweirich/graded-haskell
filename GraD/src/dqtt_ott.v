Require Import Metalib.Metatheory.
Require Export Metalib.LibLNgen.
 Require Export Qtt.usage_sig.
(** syntax *)
Definition tmvar : Set := var. (*r variables *)
Definition index : Set := nat. (*r indices *)

Definition usage : Set := usage.

Inductive tm : Set :=  (*r terms and types *)
 | a_TyUnit : tm
 | a_TmUnit : tm
 | a_letunitB (a:tm) (b:tm) (B:tm)
 | a_Pi (q:usage) (A:tm) (B:tm)
 | a_Lam (q:usage) (A:tm) (a:tm)
 | a_App (a:tm) (b:tm)
 | a_Box (q:usage) (A:tm)
 | a_LetBoxB (a:tm) (b:tm) (B:tm)
 | a_Type : tm
 | a_Var_b (_:nat)
 | a_Var_f (x:tmvar)
 | a_box (q:usage) (a:tm)
 | a_Let (a:tm) (b:tm)
 | a_Sum (A1:tm) (A2:tm)
 | a_Inj1 (a:tm)
 | a_Inj2 (a:tm)
 | a_Case (q:usage) (a:tm) (b1:tm) (b2:tm) (B:tm)
 | a_Sigma (q:usage) (A:tm) (B:tm)
 | a_Tensor (a:tm) (b:tm)
 | a_Spread (a:tm) (b:tm) (B:tm).

Inductive sort : Set :=  (*r binding classifier *)
 | Tm (A:tm).

Definition D : Set := list ( atom * sort ).

Definition context : Set := list ( atom * (usage * sort ) ).

Definition heap : Set := list ( atom * ( usage * (context * tm * tm )) ).

Definition supp : Type := atoms.

Definition n : Set := nat.

Definition qlist : Set := list usage.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_tm_wrt_tm_rec (k:nat) (a5:tm) (a_6:tm) {struct a_6}: tm :=
  match a_6 with
  | a_TyUnit => a_TyUnit 
  | a_TmUnit => a_TmUnit 
  | (a_letunitB a b B) => a_letunitB (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b) (open_tm_wrt_tm_rec k a5 B)
  | (a_Pi q A B) => a_Pi q (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_Lam q A a) => a_Lam q (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 a)
  | (a_App a b) => a_App (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b)
  | (a_Box q A) => a_Box q (open_tm_wrt_tm_rec k a5 A)
  | (a_LetBoxB a b B) => a_LetBoxB (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec (S k) a5 b) (open_tm_wrt_tm_rec k a5 B)
  | a_Type => a_Type 
  | (a_Var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => a_Var_b nat
        | inleft (right _) => a5
        | inright _ => a_Var_b (nat - 1)
      end
  | (a_Var_f x) => a_Var_f x
  | (a_box q a) => a_box q (open_tm_wrt_tm_rec k a5 a)
  | (a_Let a b) => a_Let (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_Sum A1 A2) => a_Sum (open_tm_wrt_tm_rec k a5 A1) (open_tm_wrt_tm_rec k a5 A2)
  | (a_Inj1 a) => a_Inj1 (open_tm_wrt_tm_rec k a5 a)
  | (a_Inj2 a) => a_Inj2 (open_tm_wrt_tm_rec k a5 a)
  | (a_Case q a b1 b2 B) => a_Case q (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b1) (open_tm_wrt_tm_rec k a5 b2) (open_tm_wrt_tm_rec k a5 B)
  | (a_Sigma q A B) => a_Sigma q (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_Tensor a b) => a_Tensor (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b)
  | (a_Spread a b B) => a_Spread (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec (S k) a5 b) (open_tm_wrt_tm_rec k a5 B)
end.

Definition open_sort_wrt_tm_rec (k:nat) (a5:tm) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (open_tm_wrt_tm_rec k a5 A)
end.

Definition open_sort_wrt_tm a5 sort5 := open_sort_wrt_tm_rec 0 sort5 a5.

Definition open_tm_wrt_tm a5 a_6 := open_tm_wrt_tm_rec 0 a_6 a5.

(** terms are locally-closed pre-terms *)
(** definitions *)

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
 | lc_a_Pi : forall (q:usage) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Pi q A B))
 | lc_a_Lam : forall (q:usage) (A a:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     (lc_tm (a_Lam q A a))
 | lc_a_App : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_App a b))
 | lc_a_Box : forall (q:usage) (A:tm),
     (lc_tm A) ->
     (lc_tm (a_Box q A))
 | lc_a_LetBoxB : forall (a b B:tm),
     (lc_tm a) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm B) ->
     (lc_tm (a_LetBoxB a b B))
 | lc_a_Type : 
     (lc_tm a_Type)
 | lc_a_Var_f : forall (x:tmvar),
     (lc_tm (a_Var_f x))
 | lc_a_box : forall (q:usage) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_box q a))
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
 | lc_a_Case : forall (q:usage) (a b1 b2 B:tm),
     (lc_tm a) ->
     (lc_tm b1) ->
     (lc_tm b2) ->
     (lc_tm B) ->
     (lc_tm (a_Case q a b1 b2 B))
 | lc_a_Sigma : forall (q:usage) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Sigma q A B))
 | lc_a_Tensor : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_Tensor a b))
 | lc_a_Spread : forall (a b B:tm),
     (lc_tm a) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm B) ->
     (lc_tm (a_Spread a b B)).

(* defns LC_sort *)
Inductive lc_sort : sort -> Prop :=    (* defn lc_sort *)
 | lc_Tm : forall (A:tm),
     (lc_tm A) ->
     (lc_sort (Tm A)).
(** free variables *)
Fixpoint fv_tm_tm (a5:tm) : vars :=
  match a5 with
  | a_TyUnit => {}
  | a_TmUnit => {}
  | (a_letunitB a b B) => (fv_tm_tm a) \u (fv_tm_tm b) \u (fv_tm_tm B)
  | (a_Pi q A B) => (fv_tm_tm A) \u (fv_tm_tm B)
  | (a_Lam q A a) => (fv_tm_tm A) \u (fv_tm_tm a)
  | (a_App a b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_Box q A) => (fv_tm_tm A)
  | (a_LetBoxB a b B) => (fv_tm_tm a) \u (fv_tm_tm b) \u (fv_tm_tm B)
  | a_Type => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {{x}}
  | (a_box q a) => (fv_tm_tm a)
  | (a_Let a b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_Sum A1 A2) => (fv_tm_tm A1) \u (fv_tm_tm A2)
  | (a_Inj1 a) => (fv_tm_tm a)
  | (a_Inj2 a) => (fv_tm_tm a)
  | (a_Case q a b1 b2 B) => (fv_tm_tm a) \u (fv_tm_tm b1) \u (fv_tm_tm b2) \u (fv_tm_tm B)
  | (a_Sigma q A B) => (fv_tm_tm A) \u (fv_tm_tm B)
  | (a_Tensor a b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_Spread a b B) => (fv_tm_tm a) \u (fv_tm_tm b) \u (fv_tm_tm B)
end.

Definition fv_tm_sort (sort5:sort) : vars :=
  match sort5 with
  | (Tm A) => (fv_tm_tm A)
end.

(** substitutions *)
Fixpoint subst_tm_tm (a5:tm) (x5:tmvar) (a_6:tm) {struct a_6} : tm :=
  match a_6 with
  | a_TyUnit => a_TyUnit 
  | a_TmUnit => a_TmUnit 
  | (a_letunitB a b B) => a_letunitB (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b) (subst_tm_tm a5 x5 B)
  | (a_Pi q A B) => a_Pi q (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 B)
  | (a_Lam q A a) => a_Lam q (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 a)
  | (a_App a b) => a_App (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b)
  | (a_Box q A) => a_Box q (subst_tm_tm a5 x5 A)
  | (a_LetBoxB a b B) => a_LetBoxB (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b) (subst_tm_tm a5 x5 B)
  | a_Type => a_Type 
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => (if eq_var x x5 then a5 else (a_Var_f x))
  | (a_box q a) => a_box q (subst_tm_tm a5 x5 a)
  | (a_Let a b) => a_Let (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b)
  | (a_Sum A1 A2) => a_Sum (subst_tm_tm a5 x5 A1) (subst_tm_tm a5 x5 A2)
  | (a_Inj1 a) => a_Inj1 (subst_tm_tm a5 x5 a)
  | (a_Inj2 a) => a_Inj2 (subst_tm_tm a5 x5 a)
  | (a_Case q a b1 b2 B) => a_Case q (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b1) (subst_tm_tm a5 x5 b2) (subst_tm_tm a5 x5 B)
  | (a_Sigma q A B) => a_Sigma q (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 B)
  | (a_Tensor a b) => a_Tensor (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b)
  | (a_Spread a b B) => a_Spread (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b) (subst_tm_tm a5 x5 B)
end.

Definition subst_tm_sort (a5:tm) (x5:tmvar) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (subst_tm_tm a5 x5 A)
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
  end.

Definition close_tm_wrt_tm x1 a1 := close_tm_wrt_tm_rec 0 x1 a1.


(** definitions *)

(* defns JOp *)
Inductive Step : tm -> tm -> Prop :=    (* defn Step *)
 | S_AppCong : forall (a b a':tm),
     lc_tm b ->
     Step a a' ->
     Step (a_App a b) (a_App a' b)
 | S_Beta : forall (q:usage) (A a b:tm),
     lc_tm A ->
     lc_tm (a_Lam q A a) ->
     lc_tm b ->
     Step (a_App  ( (a_Lam q A a) )  b)  (open_tm_wrt_tm  a   b ) 
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
 | S_BoxBeta : forall (q:usage) (a b B:tm),
     lc_tm (a_LetBoxB (a_box q a) b B) ->
     lc_tm B ->
     lc_tm a ->
     Step (a_LetBoxB (a_box q a) b B)  (open_tm_wrt_tm  b   a ) 
 | S_CaseCong : forall (q:usage) (a b1 b2 B a':tm),
     lc_tm b1 ->
     lc_tm b2 ->
     lc_tm B ->
     Step a a' ->
     Step (a_Case q a b1 b2 B) (a_Case q a' b1 b2 B)
 | S_Case1Beta : forall (q:usage) (a b1 b2 B:tm),
     lc_tm b2 ->
     lc_tm B ->
     lc_tm b1 ->
     lc_tm a ->
     Step (a_Case q  ( (a_Inj1 a) )  b1 b2 B) (a_App b1 a)
 | S_Case2Beta : forall (q:usage) (a b1 b2 B:tm),
     lc_tm b1 ->
     lc_tm B ->
     lc_tm b2 ->
     lc_tm a ->
     Step (a_Case q  ( (a_Inj2 a) )  b1 b2 B) (a_App b2 a)
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

(* defns JTyping *)
Inductive Typing : D -> context -> tm -> tm -> Prop :=    (* defn Typing *)
 | T_sub : forall (D5:D) (G2:context) (a A:tm) (G1:context),
     Typing D5 G1 a A ->
      ctx_sub  D5   G1   G2  ->
     Typing D5 G2 a A
 | T_type : 
     Typing  nil   nil  a_Type a_Type
 | T_var : forall (D5:D) (x:tmvar) (A:tm) (G:context),
      ~ AtomSetImpl.In  x  (dom  D5 )  ->
     Typing D5 G A a_Type ->
     Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~(  1  ,Tm  A ))  ++   (ctx_mul   0    G )   )  (a_Var_f x) A
 | T_weak : forall (D5:D) (x:tmvar) (A:tm) (G1:context) (a B:tm) (G2:context),
      ~ AtomSetImpl.In  x  (dom  D5 )  ->
     Typing D5 G1 a B ->
     Typing D5 G2 A a_Type ->
     Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~(  0  ,Tm  A ))  ++ G1 )  a B
 | T_pi : forall (L:vars) (D5:D) (G1 G2:context) (q:usage) (A B:tm) (r:usage),
     Typing D5 G1 A a_Type ->
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( r ,Tm  A ))  ++ G2 )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing D5  (ctx_plus  G1   G2 )  (a_Pi q A B) a_Type
 | T_lam : forall (L:vars) (D5:D) (G1:context) (q:usage) (A a B:tm) (G2:context),
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( q ,Tm  A ))  ++ G1 )   ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     Typing D5 G2 A a_Type ->
     Typing D5 G1 (a_Lam q A a) (a_Pi q A B)
 | T_app : forall (D5:D) (G1:context) (q:usage) (G2:context) (a b B A:tm),
     Typing D5 G1 a (a_Pi q A B) ->
     Typing D5 G2 b A ->
     Typing D5  (ctx_plus  G1     (ctx_mul  q   G2 )   )  (a_App a b)  (open_tm_wrt_tm  B   b ) 
 | T_conv : forall (D5:D) (G1:context) (a B A:tm) (G2:context),
     Typing D5 G1 a A ->
     Typing D5 G2 B a_Type ->
      Beta  A   B  ->
     Typing D5 G1 a B
 | T_unit : 
     Typing  nil   nil  a_TmUnit a_TyUnit
 | T_Unit : 
     Typing  nil   nil  a_TyUnit a_Type
 | T_UnitE : forall (L:vars) (D5:D) (G1 G2:context) (a b:tm) (r:usage) (B B1:tm) (G3:context),
     Typing D5 G1 a a_TyUnit ->
      B1 =  (open_tm_wrt_tm  B   a_TmUnit )   ->
     Typing D5 G2 b B1 ->
      ( forall y , y \notin  L  -> Typing  (  ( y  ~ Tm a_TyUnit )  ++ D5 )   (  ( y ~( r ,Tm  a_TyUnit ))  ++ G3 )   ( open_tm_wrt_tm B (a_Var_f y) )  a_Type )  ->
     Typing D5  (ctx_plus  G1   G2 )  (a_letunitB a b  ( (a_Lam r a_TyUnit B) ) )  (open_tm_wrt_tm  B   a ) 
 | T_Box : forall (D5:D) (G:context) (q:usage) (A:tm),
     Typing D5 G A a_Type ->
     Typing D5 G (a_Box q A) a_Type
 | T_box : forall (D5:D) (q:usage) (G:context) (a A:tm),
     Typing D5 G a A ->
     Typing D5  (ctx_mul  q   G )  (a_box q a) (a_Box q A)
 | T_letbox : forall (L:vars) (D5:D) (G1 G2:context) (a b:tm) (r q:usage) (A B:tm) (G3:context),
     Typing D5 G1 a (a_Box q A) ->
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( q ,Tm  A ))  ++ G2 )   ( open_tm_wrt_tm b (a_Var_f x) )   (open_tm_wrt_tm  B   (a_box q (a_Var_f x)) )  )  ->
      ( forall y , y \notin  L  -> Typing  (  ( y  ~ Tm (a_Box q A) )  ++ D5 )   (  ( y ~( r ,Tm  (a_Box q A) ))  ++ G3 )   ( open_tm_wrt_tm B (a_Var_f y) )  a_Type )  ->
     Typing D5  (ctx_plus  G1   G2 )  (a_LetBoxB a b  ( (a_Lam r (a_Box q A) B) ) )  (open_tm_wrt_tm  B   a ) 
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
 | T_case : forall (L:vars) (D5:D) (q:usage) (G1 G2:context) (a b1 b2:tm) (r:usage) (A1 A2 B B1 B2:tm) (G3:context),
      (  1   <=  q )  ->
     Typing D5 G1 a (a_Sum A1 A2) ->
      ( forall x , x \notin  L  ->   ( open_tm_wrt_tm B1 (a_Var_f x) )  =   (open_tm_wrt_tm  B   (a_Inj1 (a_Var_f x)) )    )  ->
      ( forall x , x \notin  L  ->   ( open_tm_wrt_tm B2 (a_Var_f x) )  =   (open_tm_wrt_tm  B   (a_Inj2 (a_Var_f x)) )    )  ->
     Typing D5 G2 b1 (a_Pi q A1 B1) ->
     Typing D5 G2 b2 (a_Pi q A2 B2) ->
      ( forall y , y \notin  L  -> Typing  (  ( y  ~ Tm (a_Sum A1 A2) )  ++ D5 )   (  ( y ~( r ,Tm  (a_Sum A1 A2) ))  ++ G3 )   ( open_tm_wrt_tm B (a_Var_f y) )  a_Type )  ->
     Typing D5  (ctx_plus    (ctx_mul  q   G1 )     G2 )  (a_Case q a b1 b2  ( (a_Lam r (a_Sum A1 A2) B) ) )  (open_tm_wrt_tm  B   a ) 
 | T_Sigma : forall (L:vars) (D5:D) (G1 G2:context) (q:usage) (A B:tm) (r:usage),
     Typing D5 G1 A a_Type ->
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( r ,Tm  A ))  ++ G2 )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing D5  (ctx_plus  G1   G2 )  (a_Sigma q A B) a_Type
 | T_Tensor : forall (L:vars) (D5:D) (q:usage) (G1 G2:context) (a b A B:tm) (G3:context) (r:usage),
     Typing D5 G1 a A ->
     Typing D5 G2 b  (open_tm_wrt_tm  B   a )  ->
      ( forall x , x \notin  L  -> Typing  (  ( x  ~ Tm A )  ++ D5 )   (  ( x ~( r ,Tm  A ))  ++ G3 )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing D5  (ctx_plus    (ctx_mul  q   G1 )     G2 )  (a_Tensor a b) (a_Sigma q A B)
 | T_Spread : forall (L:vars) (D5:D) (G1 G2:context) (a b:tm) (r:usage) (A B:tm) (q:usage) (A1 A2:tm) (G3:context),
      A = (a_Sigma q A1 A2)  ->
     Typing D5 G1 a A ->
      ( forall x , x \notin L -> 
        forall y, y \notin L \u {{x}} -> 
           Typing  ((x ~ Tm A1) ++ D5) ((x ~( q ,Tm A1 )) ++ G2 ) (open_tm_wrt_tm b (a_Var_f x)) 
               (a_Pi 1 (open_tm_wrt_tm A2 (a_Var_f x))
                     (close_tm_wrt_tm y (open_tm_wrt_tm B (a_Tensor (a_Var_f x) (a_Var_f y))))))  ->
      ( forall y , y \notin L -> Typing (y ~ Tm A ++ D5)  ((y ~(r , Tm A)) ++ G3)  (open_tm_wrt_tm B (a_Var_f y)) a_Type)  ->
     Typing D5  (ctx_plus G1 G2)  (a_Spread a b  (a_Lam r A B))  (open_tm_wrt_tm B a) .


(** infrastructure *)
Hint Constructors Step Typing lc_tm lc_sort : core.


