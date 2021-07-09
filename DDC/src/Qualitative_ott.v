Require Import Metalib.Metatheory. Require Export Metalib.LibLNgen. Require Export Qual.grade_sig. 
(** syntax *)
Definition tmvar : Set := var. (*r variables *)
Definition qualityvar : Set := atom. (*r qualities *)

Definition grade : Set := grade.

Inductive tm : Set :=  (*r terms and types *)
 | a_TyUnit : tm
 | a_TmUnit : tm
 | a_Pi (psi:grade) (A:tm) (B:tm)
 | a_Abs (psi:grade) (a:tm)
 | a_App (a:tm) (psi:grade) (b:tm)
 | a_Type : tm
 | a_Var_b (_:nat)
 | a_Var_f (x:tmvar)
 | a_Sum (A1:tm) (A2:tm)
 | a_Inj1 (a:tm)
 | a_Inj2 (a:tm)
 | a_Case (psi:grade) (a:tm) (b1:tm) (b2:tm)
 | a_UCase (a:tm) (b1:tm) (b2:tm)
 | a_WSigma (psi:grade) (A:tm) (B:tm)
 | a_WPair (a:tm) (psi:grade) (b:tm)
 | a_LetPair (psi:grade) (a:tm) (b:tm)
 | a_SSigma (psi:grade) (A:tm) (B:tm)
 | a_SPair (a:tm) (psi:grade) (b:tm)
 | a_Proj1 (psi:grade) (a:tm)
 | a_Proj2 (psi:grade) (a:tm).

Definition econtext : Set := list ( atom * grade ).

Definition context : Set := list ( atom * (grade * tm) ).

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
  | (a_Pi psi A B) => a_Pi psi (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_Abs psi a) => a_Abs psi (open_tm_wrt_tm_rec (S k) a5 a)
  | (a_App a psi b) => a_App (open_tm_wrt_tm_rec k a5 a) psi (open_tm_wrt_tm_rec k a5 b)
  | a_Type => a_Type 
  | (a_Var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => a_Var_b nat
        | inleft (right _) => a5
        | inright _ => a_Var_b (nat - 1)
      end
  | (a_Var_f x) => a_Var_f x
  | (a_Sum A1 A2) => a_Sum (open_tm_wrt_tm_rec k a5 A1) (open_tm_wrt_tm_rec k a5 A2)
  | (a_Inj1 a) => a_Inj1 (open_tm_wrt_tm_rec k a5 a)
  | (a_Inj2 a) => a_Inj2 (open_tm_wrt_tm_rec k a5 a)
  | (a_Case psi a b1 b2) => a_Case psi (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b1) (open_tm_wrt_tm_rec k a5 b2)
  | (a_UCase a b1 b2) => a_UCase (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b1) (open_tm_wrt_tm_rec k a5 b2)
  | (a_WSigma psi A B) => a_WSigma psi (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_WPair a psi b) => a_WPair (open_tm_wrt_tm_rec k a5 a) psi (open_tm_wrt_tm_rec k a5 b)
  | (a_LetPair psi a b) => a_LetPair psi (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_SSigma psi A B) => a_SSigma psi (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_SPair a psi b) => a_SPair (open_tm_wrt_tm_rec k a5 a) psi (open_tm_wrt_tm_rec k a5 b)
  | (a_Proj1 psi a) => a_Proj1 psi (open_tm_wrt_tm_rec k a5 a)
  | (a_Proj2 psi a) => a_Proj2 psi (open_tm_wrt_tm_rec k a5 a)
end.

Definition open_tm_wrt_tm a5 a_6 := open_tm_wrt_tm_rec 0 a_6 a5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_tm *)
Inductive lc_tm : tm -> Prop :=    (* defn lc_tm *)
 | lc_a_TyUnit : 
     (lc_tm a_TyUnit)
 | lc_a_TmUnit : 
     (lc_tm a_TmUnit)
 | lc_a_Pi : forall (psi:grade) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Pi psi A B))
 | lc_a_Abs : forall (psi:grade) (a:tm),
      ( forall x , lc_tm  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     (lc_tm (a_Abs psi a))
 | lc_a_App : forall (a:tm) (psi:grade) (b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_App a psi b))
 | lc_a_Type : 
     (lc_tm a_Type)
 | lc_a_Var_f : forall (x:tmvar),
     (lc_tm (a_Var_f x))
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
 | lc_a_Case : forall (psi:grade) (a b1 b2:tm),
     (lc_tm a) ->
     (lc_tm b1) ->
     (lc_tm b2) ->
     (lc_tm (a_Case psi a b1 b2))
 | lc_a_UCase : forall (a b1 b2:tm),
     (lc_tm a) ->
     (lc_tm b1) ->
     (lc_tm b2) ->
     (lc_tm (a_UCase a b1 b2))
 | lc_a_WSigma : forall (psi:grade) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_WSigma psi A B))
 | lc_a_WPair : forall (a:tm) (psi:grade) (b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_WPair a psi b))
 | lc_a_LetPair : forall (psi:grade) (a b:tm),
     (lc_tm a) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm (a_LetPair psi a b))
 | lc_a_SSigma : forall (psi:grade) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_SSigma psi A B))
 | lc_a_SPair : forall (a:tm) (psi:grade) (b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_SPair a psi b))
 | lc_a_Proj1 : forall (psi:grade) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Proj1 psi a))
 | lc_a_Proj2 : forall (psi:grade) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Proj2 psi a)).
(** free variables *)
Fixpoint fv_tm_tm (a5:tm) : vars :=
  match a5 with
  | a_TyUnit => {}
  | a_TmUnit => {}
  | (a_Pi psi A B) => (fv_tm_tm A) \u (fv_tm_tm B)
  | (a_Abs psi a) => (fv_tm_tm a)
  | (a_App a psi b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | a_Type => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {{x}}
  | (a_Sum A1 A2) => (fv_tm_tm A1) \u (fv_tm_tm A2)
  | (a_Inj1 a) => (fv_tm_tm a)
  | (a_Inj2 a) => (fv_tm_tm a)
  | (a_Case psi a b1 b2) => (fv_tm_tm a) \u (fv_tm_tm b1) \u (fv_tm_tm b2)
  | (a_UCase a b1 b2) => (fv_tm_tm a) \u (fv_tm_tm b1) \u (fv_tm_tm b2)
  | (a_WSigma psi A B) => (fv_tm_tm A) \u (fv_tm_tm B)
  | (a_WPair a psi b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_LetPair psi a b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_SSigma psi A B) => (fv_tm_tm A) \u (fv_tm_tm B)
  | (a_SPair a psi b) => (fv_tm_tm a) \u (fv_tm_tm b)
  | (a_Proj1 psi a) => (fv_tm_tm a)
  | (a_Proj2 psi a) => (fv_tm_tm a)
end.

(** substitutions *)
Fixpoint subst_tm_tm (a5:tm) (x5:tmvar) (a_6:tm) {struct a_6} : tm :=
  match a_6 with
  | a_TyUnit => a_TyUnit 
  | a_TmUnit => a_TmUnit 
  | (a_Pi psi A B) => a_Pi psi (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 B)
  | (a_Abs psi a) => a_Abs psi (subst_tm_tm a5 x5 a)
  | (a_App a psi b) => a_App (subst_tm_tm a5 x5 a) psi (subst_tm_tm a5 x5 b)
  | a_Type => a_Type 
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => (if eq_var x x5 then a5 else (a_Var_f x))
  | (a_Sum A1 A2) => a_Sum (subst_tm_tm a5 x5 A1) (subst_tm_tm a5 x5 A2)
  | (a_Inj1 a) => a_Inj1 (subst_tm_tm a5 x5 a)
  | (a_Inj2 a) => a_Inj2 (subst_tm_tm a5 x5 a)
  | (a_Case psi a b1 b2) => a_Case psi (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b1) (subst_tm_tm a5 x5 b2)
  | (a_UCase a b1 b2) => a_UCase (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b1) (subst_tm_tm a5 x5 b2)
  | (a_WSigma psi A B) => a_WSigma psi (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 B)
  | (a_WPair a psi b) => a_WPair (subst_tm_tm a5 x5 a) psi (subst_tm_tm a5 x5 b)
  | (a_LetPair psi a b) => a_LetPair psi (subst_tm_tm a5 x5 a) (subst_tm_tm a5 x5 b)
  | (a_SSigma psi A B) => a_SSigma psi (subst_tm_tm a5 x5 A) (subst_tm_tm a5 x5 B)
  | (a_SPair a psi b) => a_SPair (subst_tm_tm a5 x5 a) psi (subst_tm_tm a5 x5 b)
  | (a_Proj1 psi a) => a_Proj1 psi (subst_tm_tm a5 x5 a)
  | (a_Proj2 psi a) => a_Proj2 psi (subst_tm_tm a5 x5 a)
end.



(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Local Open Scope grade_scope.

Definition labels : context -> econtext :=
  map (fun '(u , s) => u).

Definition subst_ctx (a : tm) (x:var) : context -> context :=
  map (fun '(g, A) => (g, (subst_tm_tm a x A))).

Definition join_ctx_l (psi : grade) : context -> context :=    
  map (fun '(g, A) => (psi * g, A)).

Definition join_ctx_r (psi : grade) : context -> context :=
  map (fun '(g, A) => (g * psi, A)).

Definition meet_ctx_l (psi : grade) : context -> context :=
  map (fun '(g, A) => (psi + g, A)).

Definition meet_ctx_r (psi : grade) : context -> context :=
  map (fun '(g, A) => (g + psi, A)).
      

Fixpoint close_tm_wrt_tm_rec (n1 : nat) (x1 : tmvar) (a1 : tm) {struct a1} : tm :=
  match a1 with
    | a_TyUnit => a_TyUnit
    | a_TmUnit => a_TmUnit
    | a_Pi psi1 A1 B1 => a_Pi psi1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_Abs psi1 a2 => a_Abs psi1 (close_tm_wrt_tm_rec (S n1) x1 a2)
    | a_App a2 psi1 b1 => a_App (close_tm_wrt_tm_rec n1 x1 a2) psi1 (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Type => a_Type
    | a_Var_f x2 => if (x1 == x2) then (a_Var_b n1) else (a_Var_f x2)
    | a_Var_b n2 => if (lt_ge_dec n2 n1) then (a_Var_b n2) else (a_Var_b (S n2))
    | a_Sum A1 A2 => a_Sum (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec n1 x1 A2)
    | a_Inj1 a2 => a_Inj1 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Inj2 a2 => a_Inj2 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Case psi1 a2 b1 b2 => a_Case psi1 (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1) (close_tm_wrt_tm_rec n1 x1 b2)
    | a_UCase a2 b1 b2 => a_UCase (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec n1 x1 b1) (close_tm_wrt_tm_rec n1 x1 b2)
    | a_WSigma psi1 A1 B1 => a_WSigma psi1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_WPair a2 psi1 b1 => a_WPair (close_tm_wrt_tm_rec n1 x1 a2) psi1 (close_tm_wrt_tm_rec n1 x1 b1)
    | a_LetPair psi1 a2 b1 => a_LetPair psi1 (close_tm_wrt_tm_rec n1 x1 a2) (close_tm_wrt_tm_rec (S n1) x1 b1)
    | a_SSigma psi1 A1 B1 => a_SSigma psi1 (close_tm_wrt_tm_rec n1 x1 A1) (close_tm_wrt_tm_rec (S n1) x1 B1)
    | a_SPair a2 psi1 b1 => a_SPair (close_tm_wrt_tm_rec n1 x1 a2) psi1 (close_tm_wrt_tm_rec n1 x1 b1)
    | a_Proj1 psi1 a2 => a_Proj1 psi1 (close_tm_wrt_tm_rec n1 x1 a2)
    | a_Proj2 psi1 a2 => a_Proj2 psi1 (close_tm_wrt_tm_rec n1 x1 a2)
  end.

Definition close_tm_wrt_tm x1 a1 := close_tm_wrt_tm_rec 0 x1 a1.



(** definitions *)

(* defns JOp *)
Inductive Step : tm -> tm -> Prop :=    (* defn Step *)
 | S_AppCong : forall (a:tm) (psi:grade) (b a':tm),
     lc_tm b ->
     Step a a' ->
     Step (a_App a psi b) (a_App a' psi b)
 | S_Beta : forall (psi:grade) (a b:tm),
     lc_tm (a_Abs psi a) ->
     lc_tm b ->
     Step (a_App  ( (a_Abs psi a) )  psi b)  (open_tm_wrt_tm  a   b ) 
 | S_CaseCong : forall (psi:grade) (a b1 b2 a':tm),
     lc_tm b1 ->
     lc_tm b2 ->
     Step a a' ->
     Step (a_Case psi a b1 b2) (a_Case psi a' b1 b2)
 | S_Case1Beta : forall (psi:grade) (a b1 b2:tm),
     lc_tm b2 ->
     lc_tm b1 ->
     lc_tm a ->
     Step (a_Case psi  ( (a_Inj1 a) )  b1 b2) (a_App b1 psi a)
 | S_Case2Beta : forall (psi:grade) (a b1 b2:tm),
     lc_tm b1 ->
     lc_tm b2 ->
     lc_tm a ->
     Step (a_Case psi  ( (a_Inj2 a) )  b1 b2) (a_App b2 psi a)
 | S_Proj1Cong : forall (psi:grade) (a a':tm),
     Step a a' ->
     Step (a_Proj1 psi a) (a_Proj1 psi a')
 | S_Proj2Cong : forall (psi:grade) (a a':tm),
     Step a a' ->
     Step (a_Proj2 psi a) (a_Proj2 psi a')
 | S_Proj1Beta : forall (psi:grade) (a1 a2:tm),
     lc_tm a2 ->
     lc_tm a1 ->
     Step (a_Proj1 psi (a_SPair a1 psi a2)) a1
 | S_Proj2Beta : forall (psi:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
     Step (a_Proj2 psi (a_SPair a1 psi a2)) a2
 | S_LetPairCong : forall (psi:grade) (a b a':tm),
     lc_tm (a_LetPair psi a b) ->
     Step a a' ->
     Step (a_LetPair psi a b) (a_LetPair psi a' b)
 | S_LetPairBeta : forall (psi:grade) (a1 a2 b:tm),
     lc_tm (a_LetPair psi (a_WPair a1 psi a2) b) ->
     lc_tm a1 ->
     lc_tm a2 ->
     Step (a_LetPair psi (a_WPair a1 psi a2) b) (a_App  (open_tm_wrt_tm  b   a1 )   q_Bot  a2).

(* defns Jsub *)
Inductive P_sub : econtext -> econtext -> Prop :=    (* defn P_sub *)
 | P_Empty : 
     P_sub  nil   nil 
 | P_Cons : forall (P1:econtext) (x:tmvar) (psi1:grade) (P2:econtext) (psi2:grade),
      ( psi1  <=  psi2 )  ->
     P_sub P1 P2 ->
      ~ AtomSetImpl.In  x  (dom  P1 )  ->
      ~ AtomSetImpl.In  x  (dom  P2 )  ->
     P_sub  (  ( x ~ psi1 )  ++ P1 )   (  ( x ~ psi2 )  ++ P2 ) .

(* defns Wsub *)
Inductive ctx_sub : context -> context -> Prop :=    (* defn ctx_sub *)
 | CS_Empty : 
     ctx_sub  nil   nil 
 | CS_ConsTm : forall (W1:context) (x:tmvar) (psi1:grade) (A:tm) (W2:context) (psi2:grade),
      ( psi1  <=  psi2 )  ->
     ctx_sub W1 W2 ->
      ~ AtomSetImpl.In  x  (dom  W1 )  ->
      ~ AtomSetImpl.In  x  (dom  W2 )  ->
      True  ->
     ctx_sub  (  ( x ~( psi1 , A ))  ++ W1 )   (  ( x ~( psi2 , A ))  ++ W2 ) .

(* defns JGrade *)
Inductive Grade : econtext -> grade -> tm -> Prop :=    (* defn Grade *)
 | G_Type : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Grade P psi a_Type
 | G_Var : forall (P:econtext) (psi:grade) (x:tmvar) (psi0:grade),
      uniq  P  ->
      ( psi0  <=  psi )  ->
      binds  x   psi0   P  ->
     Grade P psi (a_Var_f x)
 | G_Pi : forall (L:vars) (P:econtext) (psi psi0:grade) (A B:tm),
     Grade P psi A ->
      ( forall x , x \notin  L  -> Grade  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     Grade P psi (a_Pi psi0 A B)
 | G_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (b:tm),
      ( forall x , x \notin  L  -> Grade  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     Grade P psi (a_Abs psi0 b)
 | G_AppRel : forall (P:econtext) (psi:grade) (b:tm) (psi0:grade) (a:tm),
     Grade P psi b ->
     Grade P psi a ->
      ( psi0  <=  psi )  ->
     Grade P psi (a_App b psi0 a)
 | G_AppIrrel : forall (P:econtext) (psi:grade) (b:tm) (psi0:grade) (a:tm),
     lc_tm a ->
     Grade P psi b ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     Grade P psi (a_App b psi0 a)
 | G_WSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A B:tm),
     Grade P psi A ->
      ( forall x , x \notin  L  -> Grade  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     Grade P psi (a_WSigma psi0 A B)
 | G_WPairRel : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b:tm),
     Grade P psi a ->
     Grade P psi b ->
      ( psi0  <=  psi )  ->
     Grade P psi (a_WPair a psi0 b)
 | G_WPairIrrel : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b:tm),
     lc_tm a ->
     Grade P psi b ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     Grade P psi (a_WPair a psi0 b)
 | G_LetPair : forall (L:vars) (P:econtext) (psi psi0:grade) (a c:tm),
     Grade P psi a ->
      ( forall x , x \notin  L  -> Grade  (  (  ( x ~ psi0 )  ++ P )  )  psi  ( open_tm_wrt_tm c (a_Var_f x) )  )  ->
     Grade P psi (a_LetPair psi0 a c)
 | G_SSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A B:tm),
     Grade P psi A ->
      ( forall x , x \notin  L  -> Grade  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     Grade P psi (a_SSigma psi0 A B)
 | G_SPairRel : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b:tm),
     Grade P psi a ->
     Grade P psi b ->
      ( psi0  <=  psi )  ->
     Grade P psi (a_SPair a psi0 b)
 | G_SPairIrrel : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b:tm),
     lc_tm a ->
     Grade P psi b ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     Grade P psi (a_SPair a psi0 b)
 | G_Proj1 : forall (P:econtext) (psi psi0:grade) (a:tm),
     Grade P psi a ->
      ( psi0  <=  psi )  ->
     Grade P psi (a_Proj1 psi0 a)
 | G_Proj2 : forall (P:econtext) (psi psi0:grade) (a:tm),
     Grade P psi a ->
     Grade P psi (a_Proj2 psi0 a)
 | G_Sum : forall (P:econtext) (psi:grade) (A B:tm),
     Grade P psi A ->
     Grade P psi B ->
     Grade P psi (a_Sum A B)
 | G_Inj1 : forall (P:econtext) (psi:grade) (a1:tm),
     Grade P psi a1 ->
     Grade P psi (a_Inj1 a1)
 | G_Inj2 : forall (P:econtext) (psi:grade) (a2:tm),
     Grade P psi a2 ->
     Grade P psi (a_Inj2 a2)
 | G_Case : forall (P:econtext) (psi psi0:grade) (a b1 b2:tm),
     Grade P psi a ->
     Grade P psi b1 ->
     Grade P psi b2 ->
      ( psi0  <=  psi )  ->
     Grade P psi (a_Case psi0 a b1 b2)
 | G_TyUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Grade P psi a_TyUnit
 | G_TmUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     Grade P psi a_TmUnit.

(* defns JGEq *)
Inductive CEq : econtext -> grade -> grade -> tm -> tm -> Prop :=    (* defn CEq *)
 | CEq_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     GEq P psi a1 a2 ->
     CEq P psi psi0 a1 a2
 | CEq_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
      uniq  P  ->
     CEq P psi psi0 a1 a2
with GEq : econtext -> grade -> tm -> tm -> Prop :=    (* defn GEq *)
 | GEq_Var : forall (P:econtext) (psi:grade) (x:tmvar) (psi0:grade),
      uniq  P  ->
      binds  x   psi0   P  ->
      ( psi0  <=  psi )  ->
     GEq P psi (a_Var_f x) (a_Var_f x)
 | GEq_Type : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GEq P psi a_Type a_Type
 | GEq_Pi : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 B1 A2 B2:tm),
     GEq P psi A1 A2 ->
      ( forall x , x \notin  L  -> GEq  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     GEq P psi (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2)
 | GEq_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (b1 b2:tm),
      ( forall x , x \notin  L  -> GEq  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     GEq P psi (a_Abs psi0 b1) (a_Abs psi0 b2)
 | GEq_App : forall (P:econtext) (psi:grade) (b1:tm) (psi0:grade) (a1 b2 a2:tm),
     GEq P psi b1 b2 ->
     CEq P psi psi0 a1 a2 ->
     GEq P psi (a_App b1 psi0 a1) (a_App b2 psi0 a2)
 | GEq_WSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 B1 A2 B2:tm),
     GEq P psi A1 A2 ->
      ( forall x , x \notin  L  -> GEq  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     GEq P psi (a_WSigma psi0 A1 B1) (a_WSigma psi0 A2 B2)
 | GEq_WPair : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     CEq P psi psi0 a1 a2 ->
     GEq P psi b1 b2 ->
     GEq P psi (a_WPair a1 psi0 b1) (a_WPair a2 psi0 b2)
 | GEq_LetPair : forall (L:vars) (P:econtext) (psi psi0:grade) (a1 b1 a2 b2:tm),
     GEq P psi a1 a2 ->
      ( forall x , x \notin  L  -> GEq   (  ( x ~ psi0 )  ++ P )   psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     GEq P psi (a_LetPair psi0 a1 b1) (a_LetPair psi0 a2 b2)
 | GEq_SSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 B1 A2 B2:tm),
     GEq P psi A1 A2 ->
      ( forall x , x \notin  L  -> GEq  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     GEq P psi (a_SSigma psi0 A1 B1) (a_SSigma psi0 A2 B2)
 | GEq_SPair : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     CEq P psi psi0 a1 a2 ->
     GEq P psi b1 b2 ->
     GEq P psi (a_SPair a1 psi0 b1) (a_SPair a2 psi0 b2)
 | GEq_Proj1 : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     GEq P psi a1 a2 ->
      ( psi0  <=  psi )  ->
     GEq P psi (a_Proj1 psi0 a1) (a_Proj1 psi0 a2)
 | GEq_Proj2 : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     GEq P psi a1 a2 ->
     GEq P psi (a_Proj2 psi0 a1) (a_Proj2 psi0 a2)
 | GEq_Sum : forall (P:econtext) (psi:grade) (A1 A2 A1' A2':tm),
     GEq P psi A1 A1' ->
     GEq P psi A2 A2' ->
     GEq P psi (a_Sum A1 A2) (a_Sum A1' A2')
 | GEq_Inj1 : forall (P:econtext) (psi:grade) (a1 a1':tm),
     GEq P psi a1 a1' ->
     GEq P psi (a_Inj1 a1) (a_Inj1 a1')
 | GEq_Inj2 : forall (P:econtext) (psi:grade) (a2 a2':tm),
     GEq P psi a2 a2' ->
     GEq P psi (a_Inj2 a2) (a_Inj2 a2')
 | GEq_Case : forall (P:econtext) (psi psi0:grade) (a b1 b2 a' b1' b2':tm),
     GEq P psi a a' ->
     GEq P psi b1 b1' ->
     GEq P psi b2 b2' ->
      ( psi0  <=  psi )  ->
     GEq P psi (a_Case psi0 a b1 b2) (a_Case psi0 a' b1' b2')
 | GEq_TyUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GEq P psi a_TyUnit a_TyUnit
 | GEq_TmUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     GEq P psi a_TmUnit a_TmUnit.

(* defns JUnTyDefEq *)
Inductive DefEq : econtext -> grade -> tm -> tm -> Prop :=    (* defn DefEq *)
 | Eq_Refl : forall (P:econtext) (psi:grade) (a:tm),
     Grade P psi a ->
     DefEq P psi a a
 | Eq_Trans : forall (P:econtext) (psi:grade) (a c b:tm),
     DefEq P psi a b ->
     DefEq P psi b c ->
     DefEq P psi a c
 | Eq_Sym : forall (P:econtext) (psi:grade) (b a:tm),
     DefEq P psi a b ->
     DefEq P psi b a
 | Eq_Beta : forall (P:econtext) (psi:grade) (a b:tm),
     Grade P psi a ->
     Step a b ->
     Grade P psi b ->
     DefEq P psi a b
 | Eq_Pi : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 B1 A2 B2:tm),
     DefEq P psi A1 A2 ->
      ( forall x , x \notin  L  -> DefEq  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     DefEq P psi (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2)
 | Eq_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (b1 b2:tm),
      ( forall x , x \notin  L  -> DefEq  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     DefEq P psi (a_Abs psi0 b1) (a_Abs psi0 b2)
 | Eq_AppRel : forall (P:econtext) (psi:grade) (b1:tm) (psi0:grade) (a1 b2 a2:tm),
     DefEq P psi b1 b2 ->
     DefEq P psi a1 a2 ->
      ( psi0  <=  psi )  ->
     DefEq P psi (a_App b1 psi0 a1) (a_App b2 psi0 a2)
 | Eq_AppIrrel : forall (P:econtext) (psi:grade) (b1:tm) (psi0:grade) (a1 b2 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
     DefEq P psi b1 b2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     DefEq P psi (a_App b1 psi0 a1) (a_App b2 psi0 a2)
 | Eq_PiFst : forall (P:econtext) (psi:grade) (A1 A2:tm) (psi0:grade) (B1 B2:tm),
     DefEq P psi (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2) ->
     DefEq P psi A1 A2
 | Eq_PiSnd : forall (P:econtext) (psi:grade) (B1 a1 B2 a2:tm) (psi0:grade) (A1 A2:tm),
     DefEq P psi (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2) ->
     DefEq P psi a1 a2 ->
     DefEq P psi  (open_tm_wrt_tm  B1   a1 )   (open_tm_wrt_tm  B2   a2 ) 
 | Eq_WSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 B1 A2 B2:tm),
     DefEq P psi A1 A2 ->
      ( forall x , x \notin  L  -> DefEq  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     DefEq P psi (a_WSigma psi0 A1 B1) (a_WSigma psi0 A2 B2)
 | Eq_WSigmaFst : forall (P:econtext) (psi:grade) (A1 A2:tm) (psi0:grade) (B1 B2:tm),
     DefEq P psi (a_WSigma psi0 A1 B1) (a_WSigma psi0 A2 B2) ->
     DefEq P psi A1 A2
 | Eq_WSigmaSnd : forall (P:econtext) (psi:grade) (B1 a B2:tm) (psi0:grade) (A1 A2:tm),
     DefEq P psi (a_WSigma psi0 A1 B1) (a_WSigma psi0 A2 B2) ->
     Grade P psi a ->
     DefEq P psi  (open_tm_wrt_tm  B1   a )   (open_tm_wrt_tm  B2   a ) 
 | Eq_WPairRel : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     DefEq P psi a1 a2 ->
     DefEq P psi b1 b2 ->
      ( psi0  <=  psi )  ->
     DefEq P psi (a_WPair a1 psi0 b1) (a_WPair a2 psi0 b2)
 | Eq_WPairIrrel : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
     DefEq P psi b1 b2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     DefEq P psi (a_WPair a1 psi0 b1) (a_WPair a2 psi0 b2)
 | Eq_LetPair : forall (L:vars) (P:econtext) (psi psi0:grade) (a1 b1 a2 b2:tm),
     DefEq P psi a1 a2 ->
      ( forall x , x \notin  L  -> DefEq   (  ( x ~ psi0 )  ++ P )   psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     DefEq P psi (a_LetPair psi0 a1 b1) (a_LetPair psi0 a2 b2)
 | Eq_SSigma : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 B1 A2 B2:tm),
     DefEq P psi A1 A2 ->
      ( forall x , x \notin  L  -> DefEq  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     DefEq P psi (a_SSigma psi0 A1 B1) (a_SSigma psi0 A2 B2)
 | Eq_SSigmaFst : forall (P:econtext) (psi:grade) (A1 A2:tm) (psi0:grade) (B1 B2:tm),
     DefEq P psi (a_SSigma psi0 A1 B1) (a_SSigma psi0 A2 B2) ->
     DefEq P psi A1 A2
 | Eq_SSigmaSnd : forall (P:econtext) (psi:grade) (B1 a1 B2 a2:tm) (psi0:grade) (A1 A2:tm),
     DefEq P psi (a_SSigma psi0 A1 B1) (a_SSigma psi0 A2 B2) ->
     DefEq P psi a1 a2 ->
     DefEq P psi  (open_tm_wrt_tm  B1   a1 )   (open_tm_wrt_tm  B2   a2 ) 
 | Eq_SPairRel : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
      ( psi0  <=  psi )  ->
     DefEq P psi a1 a2 ->
     DefEq P psi b1 b2 ->
     DefEq P psi (a_SPair a1 psi0 b1) (a_SPair a2 psi0 b2)
 | Eq_SPairIrrel : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     DefEq P psi b1 b2 ->
     DefEq P psi (a_SPair a1 psi0 b1) (a_SPair a2 psi0 b2)
 | Eq_Proj1 : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     DefEq P psi a1 a2 ->
      ( psi0  <=  psi )  ->
     DefEq P psi (a_Proj1 psi0 a1) (a_Proj1 psi0 a2)
 | Eq_Proj2 : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     DefEq P psi a1 a2 ->
     DefEq P psi (a_Proj2 psi0 a1) (a_Proj2 psi0 a2)
 | Eq_Sum : forall (P:econtext) (psi:grade) (A1 A2 A1' A2':tm),
     DefEq P psi A1 A1' ->
     DefEq P psi A2 A2' ->
     DefEq P psi (a_Sum A1 A2) (a_Sum A1' A2')
 | Eq_SumFst : forall (P:econtext) (psi:grade) (A1 A1' A2 A2':tm),
     DefEq P psi (a_Sum A1 A2) (a_Sum A1' A2') ->
     DefEq P psi A1 A1'
 | Eq_SumSnd : forall (P:econtext) (psi:grade) (A2 A2' A1 A1':tm),
     DefEq P psi (a_Sum A1 A2) (a_Sum A1' A2') ->
     DefEq P psi A2 A2'
 | Eq_Inj1 : forall (P:econtext) (psi:grade) (a1 a1':tm),
     DefEq P psi a1 a1' ->
     DefEq P psi (a_Inj1 a1) (a_Inj1 a1')
 | Eq_Inj2 : forall (P:econtext) (psi:grade) (a2 a2':tm),
     DefEq P psi a2 a2' ->
     DefEq P psi (a_Inj2 a2) (a_Inj2 a2')
 | Eq_Case : forall (P:econtext) (psi psi0:grade) (a b1 b2 a' b1' b2':tm),
     DefEq P psi a a' ->
     DefEq P psi b1 b1' ->
     DefEq P psi b2 b2' ->
      ( psi0  <=  psi )  ->
     DefEq P psi (a_Case psi0 a b1 b2) (a_Case psi0 a' b1' b2')
 | Eq_TyUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     DefEq P psi a_TyUnit a_TyUnit
 | Eq_TmUnit : forall (P:econtext) (psi:grade),
      uniq  P  ->
     DefEq P psi a_TmUnit a_TmUnit
 | Eq_SubstIrrel : forall (L:vars) (P:econtext) (phi:grade) (b1 a1 b2 a2:tm) (psi:grade),
     lc_tm a1 ->
     lc_tm a2 ->
      True  ->
      True  ->
      ( forall x , x \notin  L  -> DefEq  (  ( x ~ psi )  ++ P )  phi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
      not (  (  ( psi  <=  phi )  )  )  ->
     DefEq P phi  (open_tm_wrt_tm  b1   a1 )   (open_tm_wrt_tm  b2   a2 ) .

(* defns JTyping *)
Inductive Typing : context -> grade -> tm -> tm -> Prop :=    (* defn Typing *)
 | T_Type : forall (W:context) (psi:grade),
      uniq  W  ->
      ( psi  <=   q_C  )  ->
     Typing W psi a_Type a_Type
 | T_Conv : forall (W:context) (psi:grade) (a B A:tm),
     Typing W psi a A ->
     DefEq  (labels   (meet_ctx_l   q_C    W )  )   q_C  A B ->
     Typing  (meet_ctx_l   q_C    W )   q_C  B a_Type ->
     Typing W psi a B
 | T_Var : forall (W:context) (psi:grade) (x:tmvar) (A:tm) (psi0:grade),
      uniq  W  ->
      ( psi0  <=  psi )  ->
      binds  x  ( psi0 ,  A )  W  ->
      ( psi  <=   q_C  )  ->
     Typing W psi (a_Var_f x) A
 | T_Pi : forall (L:vars) (W:context) (psi psi0:grade) (A B:tm),
     Typing W psi A a_Type ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~( psi , A ))  ++ W )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing W psi (a_Pi psi0 A B) a_Type
 | T_Abs : forall (L:vars) (W:context) (psi psi0:grade) (b A B:tm),
      ( forall x , x \notin  L  -> Typing  (  ( x ~(  (q_join  psi0   psi )  , A ))  ++ W )  psi  ( open_tm_wrt_tm b (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     Typing  (meet_ctx_l   q_C    W )   q_C   ( (a_Pi psi0 A B) )  a_Type ->
     Typing W psi (a_Abs psi0 b) (a_Pi psi0 A B)
 | T_App : forall (W:context) (psi:grade) (b:tm) (psi0:grade) (a B A:tm),
     Typing W psi b (a_Pi psi0 A B) ->
     Typing W  (q_join  psi0   psi )  a A ->
      ( psi0  <=   q_C  )  ->
     Typing W psi (a_App b psi0 a)  (open_tm_wrt_tm  B   a ) 
 | T_AppIrrel : forall (W:context) (psi:grade) (b:tm) (psi0:grade) (a B A:tm),
     Typing W psi b (a_Pi psi0 A B) ->
     Typing  (meet_ctx_l   q_C    W )   q_C  a A ->
      (  q_C   <  psi0 )  ->
     Typing W psi (a_App b psi0 a)  (open_tm_wrt_tm  B   a ) 
 | T_WSigma : forall (L:vars) (W:context) (psi psi0:grade) (A B:tm),
     Typing W psi A a_Type ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~( psi , A ))  ++ W )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing W psi (a_WSigma psi0 A B) a_Type
 | T_WPair : forall (W:context) (psi:grade) (a:tm) (psi0:grade) (b A B:tm),
     Typing  (meet_ctx_l   q_C    W )   q_C   ( (a_WSigma psi0 A B) )  a_Type ->
     Typing W  (q_join  psi0   psi )  a A ->
     Typing W psi b  (open_tm_wrt_tm  B   a )  ->
      ( psi0  <=   q_C  )  ->
     Typing W psi (a_WPair a psi0 b) (a_WSigma psi0 A B)
 | T_WPairIrrel : forall (W:context) (psi:grade) (a:tm) (psi0:grade) (b A B:tm),
     Typing  (meet_ctx_l   q_C    W )   q_C   ( (a_WSigma psi0 A B) )  a_Type ->
     Typing  (meet_ctx_l   q_C    W )   q_C  a A ->
      (  q_C   <  psi0 )  ->
     Typing W psi b  (open_tm_wrt_tm  B   a )  ->
     Typing W psi (a_WPair a psi0 b) (a_WSigma psi0 A B)
 | T_LetPair : forall (L:vars) (W:context) (psi psi0:grade) (a c C B A:tm),
      ( forall x , x \notin  L  ->
              Typing ((x ~ (q_C, a_WSigma psi0 A B)) ++ meet_ctx_l q_C W) q_C (open_tm_wrt_tm C (a_Var_f x)) a_Type)  ->
      Typing W psi a (a_WSigma psi0 A B) ->
      ( forall x , x \notin  L  ->
        forall y,  y \notin L \u {{x}} ->
              Typing ((x ~ ((q_join psi0 psi), A)) ++ W) psi (open_tm_wrt_tm c (a_Var_f x))
                   (a_Pi q_Bot (open_tm_wrt_tm B (a_Var_f x))
                          (close_tm_wrt_tm y (open_tm_wrt_tm C (a_WPair (a_Var_f x) psi0 (a_Var_f y)))))) ->
      (Typing W psi (a_LetPair psi0 a c)  (open_tm_wrt_tm C a))
 | T_SSigma : forall (L:vars) (W:context) (psi psi0:grade) (A B:tm),
     Typing W psi A a_Type ->
      ( forall x , x \notin  L  -> Typing  (  ( x ~( psi , A ))  ++ W )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  a_Type )  ->
     Typing W psi (a_SSigma psi0 A B) a_Type
 | T_SPair : forall (W:context) (psi:grade) (a:tm) (psi0:grade) (b A B:tm),
     Typing  (meet_ctx_l   q_C    W )   q_C  (a_SSigma psi0 A B) a_Type ->
     Typing W  (q_join  psi0   psi )  a A ->
     Typing W psi b  (open_tm_wrt_tm  B   a )  ->
      ( psi0  <=   q_C  )  ->
     Typing W psi (a_SPair a psi0 b) (a_SSigma psi0 A B)
 | T_Proj1 : forall (W:context) (psi psi0:grade) (a A B:tm),
     Typing W psi a (a_SSigma psi0 A B) ->
      ( psi0  <=  psi )  ->
     Typing W psi (a_Proj1 psi0 a) A
 | T_Proj2 : forall (W:context) (psi psi0:grade) (a B A:tm),
     Typing W psi a (a_SSigma psi0 A B) ->
      ( psi0  <=   q_C  )  ->
     Typing W psi (a_Proj2 psi0 a)  (open_tm_wrt_tm  B   (a_Proj1 psi0 a) ) 
 | T_Sum : forall (W:context) (psi:grade) (A B:tm),
     Typing W psi A a_Type ->
     Typing W psi B a_Type ->
     Typing W psi (a_Sum A B) a_Type
 | T_Inj1 : forall (W:context) (psi:grade) (a1 A1 A2:tm),
     Typing W psi a1 A1 ->
     Typing  (meet_ctx_l   q_C    W )   q_C  A2 a_Type ->
     Typing W psi (a_Inj1 a1) (a_Sum A1 A2)
 | T_Inj2 : forall (W:context) (psi:grade) (a2 A1 A2:tm),
     Typing W psi a2 A2 ->
     Typing  (meet_ctx_l   q_C    W )   q_C  A1 a_Type ->
     Typing W psi (a_Inj2 a2) (a_Sum A1 A2)
 | T_Case : forall (L:vars) (W:context) (psi psi0:grade) (a b1 b2 B:tm) (A1 A2 B1 B2:tm),
      ( forall z, z \notin    L ->  Typing  (  (  ( z ~(  q_C  , (a_Sum A1 A2) ))  ++  (  (meet_ctx_l   q_C    W )  )  )  )   q_C  (open_tm_wrt_tm B (a_Var_f z)) a_Type) ->
     Typing W psi a (a_Sum A1 A2) ->
      ( forall x , x \notin  L  ->   ( open_tm_wrt_tm B1 (a_Var_f x) )  =   (open_tm_wrt_tm  B   (a_Inj1 (a_Var_f x)) )    )  ->
      ( forall y , y \notin  L  ->   ( open_tm_wrt_tm B2 (a_Var_f y) )  =   (open_tm_wrt_tm  B   (a_Inj2 (a_Var_f y)) )    )  ->
     Typing W psi b1 (a_Pi psi0 A1 B1) ->
     Typing W psi b2 (a_Pi psi0 A2 B2) ->
      ( psi0  <=  psi )  ->
     Typing W psi (a_Case psi0 a b1 b2)  (open_tm_wrt_tm  B   a ) 
 | T_TmUnit : forall (W:context) (psi:grade),
      uniq  W  ->
      ( psi  <=   q_C  )  ->
     Typing W psi a_TyUnit a_Type
 | T_TyUnit : forall (W:context) (psi:grade),
      uniq  W  ->
      ( psi  <=   q_C  )  ->
     Typing W psi a_TmUnit a_TyUnit.

(* defns JCTyping *)
Inductive CTyping : context -> grade -> tm -> tm -> Prop :=    (* defn CTyping *)
 | CT_Leq : forall (W:context) (psi:grade) (a A:tm),
     Typing W psi a A ->
      ( psi  <=   q_C  )  ->
     CTyping W psi a A
 | CT_Top : forall (W:context) (psi:grade) (a A:tm),
     Typing  (meet_ctx_l   q_C    W )   q_C  a A ->
      (  q_C   <  psi )  ->
     CTyping W psi a A.

(* defns JCtx *)
Inductive Ctx : context -> Prop :=    (* defn Ctx *)
 | Ctx_Empty : 
     Ctx  nil 
 | Ctx_Cons : forall (W:context) (x:tmvar) (psi0:grade) (A:tm),
     Ctx W ->
     Typing  (meet_ctx_l   q_C    W )   q_C  A a_Type ->
      ~ AtomSetImpl.In  x  (dom  W )  ->
     Ctx  (  ( x ~( psi0 , A ))  ++ W ) .

(* defns JValueType *)
Inductive ValueType : tm -> Prop :=    (* defn ValueType *)
 | ValueType_Type : 
     ValueType a_Type
 | ValueType_Unit : 
     ValueType a_TyUnit
 | ValueType_Pi : forall (psi:grade) (A B:tm),
     lc_tm A ->
     lc_tm (a_Pi psi A B) ->
     ValueType (a_Pi psi A B)
 | ValueType_WSigma : forall (psi:grade) (A B:tm),
     lc_tm A ->
     lc_tm (a_WSigma psi A B) ->
     ValueType (a_WSigma psi A B)
 | ValueType_SSigma : forall (psi:grade) (A B:tm),
     lc_tm A ->
     lc_tm (a_SSigma psi A B) ->
     ValueType (a_SSigma psi A B)
 | ValueType_Sum : forall (A B:tm),
     lc_tm A ->
     lc_tm B ->
     ValueType (a_Sum A B).

(* defns JConsistent *)
Inductive Consistent : tm -> tm -> Prop :=    (* defn Consistent *)
 | Consistent_a_Type : 
     Consistent a_Type a_Type
 | Consistent_a_Unit : 
     Consistent a_TyUnit a_TyUnit
 | Consistent_a_Pi : forall (psi:grade) (A B A' B':tm),
     lc_tm A ->
     lc_tm (a_Pi psi A B) ->
     lc_tm A' ->
     lc_tm (a_Pi psi A' B') ->
     Consistent  ( (a_Pi psi A B) )   ( (a_Pi psi A' B') ) 
 | Consistent_a_WSigma : forall (psi:grade) (A B A' B':tm),
     lc_tm A ->
     lc_tm (a_WSigma psi A B) ->
     lc_tm A' ->
     lc_tm (a_WSigma psi A' B') ->
     Consistent  ( (a_WSigma psi A B) )   ( (a_WSigma psi A' B') ) 
 | Consistent_a_SSigma : forall (psi:grade) (A B A' B':tm),
     lc_tm A ->
     lc_tm (a_SSigma psi A B) ->
     lc_tm A' ->
     lc_tm (a_SSigma psi A' B') ->
     Consistent  (a_SSigma psi A B)   (a_SSigma psi A' B') 
 | Consistent_a_Sum : forall (A B A' B':tm),
     lc_tm A ->
     lc_tm B ->
     lc_tm A' ->
     lc_tm B' ->
     Consistent  ( (a_Sum A B) )   ( (a_Sum A' B') ) 
 | Consistent_a_Step_R : forall (a b:tm),
     lc_tm b ->
      not ( ValueType a )  ->
     Consistent a b
 | Consistent_a_Step_L : forall (a b:tm),
     lc_tm a ->
      not ( ValueType b )  ->
     Consistent a b.

(* defns JPar *)
Inductive Par : econtext -> grade -> tm -> tm -> Prop :=    (* defn Par *)
 | Par_Refl : forall (P:econtext) (psi:grade) (a:tm),
     Grade P psi a ->
     Par P psi a a
 | Par_Pi : forall (L:vars) (P:econtext) (psi psi1:grade) (A1 B1 A2 B2:tm),
     Par P psi A1 A2 ->
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     Par P psi (a_Pi psi1 A1 B1) (a_Pi psi1 A2 B2)
 | Par_AppBetaRel : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b':tm),
     Par P psi a  ( (a_Abs psi0 a') )  ->
     Par P psi b b' ->
      ( psi0  <=  psi )  ->
     Par P psi (a_App a psi0 b)  (open_tm_wrt_tm  a'   b' ) 
 | Par_AppBetaIrrel : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b':tm),
     lc_tm b ->
     lc_tm b' ->
     Par P psi a  ( (a_Abs psi0 a') )  ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     Par P psi (a_App a psi0 b)  (open_tm_wrt_tm  a'   b' ) 
 | Par_AppRel : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b':tm),
     Par P psi a a' ->
     Par P psi b b' ->
      ( psi0  <=  psi )  ->
     Par P psi (a_App a psi0 b) (a_App a' psi0 b')
 | Par_AppIrrel : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b':tm),
     lc_tm b ->
     lc_tm b' ->
     Par P psi a a' ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     Par P psi (a_App a psi0 b) (a_App a' psi0 b')
 | Par_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (b1 b2:tm),
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     Par P psi (a_Abs psi0 b1) (a_Abs psi0 b2)
 | Par_WSigma : forall (L:vars) (P:econtext) (psi psi1:grade) (A1 B1 A2 B2:tm),
     Par P psi A1 A2 ->
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     Par P psi (a_WSigma psi1 A1 B1) (a_WSigma psi1 A2 B2)
 | Par_WPairRel : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     Par P psi a1 a2 ->
     Par P psi b1 b2 ->
      ( psi0  <=  psi )  ->
     Par P psi (a_WPair a1 psi0 b1) (a_WPair a2 psi0 b2)
 | Par_WPairIrrel : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
     Par P psi b1 b2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     Par P psi (a_WPair a1 psi0 b1) (a_WPair a2 psi0 b2)
 | Par_WPairBeta : forall (L:vars) (P:econtext) (psi psi0:grade) (a1 b1 b2 a1' a2':tm),
     Par P psi a1 (a_WPair a1' psi0 a2') ->
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   (open_tm_wrt_tm  b2   (a_Var_f x) )  )  ->
     Par P psi (a_LetPair psi0 a1 b1) (a_App  (open_tm_wrt_tm  b2   a1' )   q_Bot  a2')
 | Par_LetPair : forall (L:vars) (P:econtext) (psi psi0:grade) (a1 b1 a2 b2:tm),
     Par P psi a1 a2 ->
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi0 )  ++ P )  psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     Par P psi (a_LetPair psi0 a1 b1) (a_LetPair psi0 a2 b2)
 | Par_SSigma : forall (L:vars) (P:econtext) (psi psi1:grade) (A1 B1 A2 B2:tm),
     Par P psi A1 A2 ->
      ( forall x , x \notin  L  -> Par  (  ( x ~ psi )  ++ P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     Par P psi (a_SSigma psi1 A1 B1) (a_SSigma psi1 A2 B2)
 | Par_SPairRel : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     Par P psi a1 a2 ->
     Par P psi b1 b2 ->
      ( psi0  <=  psi )  ->
     Par P psi (a_SPair a1 psi0 b1) (a_SPair a2 psi0 b2)
 | Par_SPairIrrel : forall (P:econtext) (psi:grade) (a1:tm) (psi0:grade) (b1 a2 b2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
     Par P psi b1 b2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     Par P psi (a_SPair a1 psi0 b1) (a_SPair a2 psi0 b2)
 | Par_Proj1Beta : forall (P:econtext) (psi psi0:grade) (a1 a1' a2:tm),
     Par P psi a1 (a_SPair a1' psi0 a2) ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Proj1 psi0 a1) a1'
 | Par_Proj1 : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     Par P psi a1 a2 ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Proj1 psi0 a1) (a_Proj1 psi0 a2)
 | Par_Proj2Beta : forall (P:econtext) (psi psi0:grade) (a1 a2 a1':tm),
     Par P psi a1 (a_SPair a1' psi0 a2) ->
     Par P psi (a_Proj2 psi0 a1) a2
 | Par_Proj2 : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     Par P psi a1 a2 ->
     Par P psi (a_Proj2 psi0 a1) (a_Proj2 psi0 a2)
 | Par_Sum : forall (P:econtext) (psi:grade) (A1 A2 A1' A2':tm),
     Par P psi A1 A1' ->
     Par P psi A2 A2' ->
     Par P psi (a_Sum A1 A2) (a_Sum A1' A2')
 | Par_Inj1 : forall (P:econtext) (psi:grade) (a1 a1':tm),
     Par P psi a1 a1' ->
     Par P psi (a_Inj1 a1) (a_Inj1 a1')
 | Par_Inj2 : forall (P:econtext) (psi:grade) (a2 a2':tm),
     Par P psi a2 a2' ->
     Par P psi (a_Inj2 a2) (a_Inj2 a2')
 | Par_CaseBeta1 : forall (P:econtext) (psi psi0:grade) (a b1 b2 b1' a' b2':tm),
     Par P psi a (a_Inj1 a') ->
     Par P psi b1 b1' ->
     Par P psi b2 b2' ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Case psi0 a b1 b2) (a_App b1' psi0 a')
 | Par_CaseBeta2 : forall (P:econtext) (psi psi0:grade) (a b1 b2 b2' a' b1':tm),
     Par P psi a (a_Inj2 a') ->
     Par P psi b1 b1' ->
     Par P psi b2 b2' ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Case psi0 a b1 b2) (a_App b2' psi0 a')
 | Par_Case : forall (P:econtext) (psi psi0:grade) (a b1 b2 a' b1' b2':tm),
     Par P psi a a' ->
     Par P psi b1 b1' ->
     Par P psi b2 b2' ->
      ( psi0  <=  psi )  ->
     Par P psi (a_Case psi0 a b1 b2) (a_Case psi0 a' b1' b2').

(* defns JMultiPar *)
Inductive MultiPar : econtext -> grade -> tm -> tm -> Prop :=    (* defn MultiPar *)
 | MP_Refl : forall (P:econtext) (psi:grade) (a:tm),
     Grade P psi a ->
     MultiPar P psi a a
 | MP_Step : forall (P:econtext) (psi:grade) (a a' b:tm),
     Par P psi a b ->
     MultiPar P psi b a' ->
     MultiPar P psi a a'.

(* defns JJoins *)
Inductive Joins : econtext -> grade -> tm -> tm -> Prop :=    (* defn Joins *)
 | join : forall (P:econtext) (psi:grade) (a1 a2 b1 b2:tm),
     MultiPar P psi a1 b1 ->
     MultiPar P psi a2 b2 ->
     GEq P psi b1 b2 ->
     Joins P psi a1 a2.

(* defns JValue *)
Inductive Value : tm -> Prop :=    (* defn Value *)
 | V_ValueType : forall (a:tm),
     ValueType a ->
     Value a
 | V_TmUnit : 
     Value a_TmUnit
 | V_Abs : forall (psi:grade) (a:tm),
     lc_tm (a_Abs psi a) ->
     Value (a_Abs psi a)
 | V_WPair : forall (a:tm) (psi:grade) (b:tm),
     lc_tm a ->
     lc_tm b ->
     Value (a_WPair a psi b)
 | V_SPair : forall (a:tm) (psi:grade) (b:tm),
     lc_tm a ->
     lc_tm b ->
     Value (a_SPair a psi b)
 | V_Inj1 : forall (a:tm),
     lc_tm a ->
     Value (a_Inj1 a)
 | V_Inj2 : forall (a:tm),
     lc_tm a ->
     Value (a_Inj2 a).

(* defns JCGrade *)
Inductive CGrade : econtext -> grade -> grade -> tm -> Prop :=    (* defn CGrade *)
 | CG_Leq : forall (P:econtext) (phi phi0:grade) (a:tm),
      ( phi0  <=  phi )  ->
     Grade P phi a ->
     CGrade P phi phi0 a
 | CG_Nleq : forall (P:econtext) (phi phi0:grade) (a:tm),
     lc_tm a ->
      not (  (  ( phi0  <=  phi )  )  )  ->
     CGrade P phi phi0 a.

(* defns JCDefEq *)
Inductive CDefEq : econtext -> grade -> grade -> tm -> tm -> Prop :=    (* defn CDefEq *)
 | CDefEq_Leq : forall (P:econtext) (phi phi0:grade) (a b:tm),
      ( phi0  <=  phi )  ->
     DefEq P phi a b ->
     CDefEq P phi phi0 a b
 | CDefEq_Nleq : forall (P:econtext) (phi phi0:grade) (a b:tm),
     lc_tm a ->
     lc_tm b ->
      not (  (  ( phi0  <=  phi )  )  )  ->
     CDefEq P phi phi0 a b.

(* defns JCPar *)
Inductive CPar : econtext -> grade -> grade -> tm -> tm -> Prop :=    (* defn CPar *)
 | CPar_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     Par P psi a1 a2 ->
     CPar P psi psi0 a1 a2
 | CPar_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
      uniq  P  ->
     CPar P psi psi0 a1 a2.

(* defns JCMultiPar *)
Inductive CMultiPar : econtext -> grade -> grade -> tm -> tm -> Prop :=    (* defn CMultiPar *)
 | CMP_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     MultiPar P psi a1 a2 ->
     CMultiPar P psi psi0 a1 a2
 | CMP_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
      uniq  P  ->
     CMultiPar P psi psi0 a1 a2.

(* defns JCJoins *)
Inductive CJoins : econtext -> grade -> grade -> tm -> tm -> Prop :=    (* defn CJoins *)
 | CJ_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     Joins P psi a1 a2 ->
     CJoins P psi psi0 a1 a2
 | CJ_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
      uniq  P  ->
     CJoins P psi psi0 a1 a2.


(** infrastructure *)
Hint Constructors Step P_sub ctx_sub Grade CEq GEq DefEq Typing CTyping Ctx ValueType Consistent Par MultiPar Joins Value CGrade CDefEq CPar CMultiPar CJoins lc_tm : core.


