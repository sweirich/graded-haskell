Require Import Qtt.dqtt_ott.
Require Import Qtt.dqtt_inf.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : context => dom x) in
  let D := gather_atoms_with (fun x => fv_tm_tm x) in
  let E := gather_atoms_with (fun x : list (atom * sort) => dom x) in

  constr:(A \u B \u C \u D \u E).


Ltac invert_equality := 
  repeat match goal with 
    | [H : (_,_) = (_,_) |- _ ] => inversion H; subst; clear H
    | [H : (_,_,_) = (_,_,_) |- _ ] => inversion H; subst; clear H
    | [H : (_,_,_,_) = (_,_,_,_) |- _ ] => inversion H; subst; clear H
    | [H : [_] ++ _ = [_] ++ _ |- _ ] => inversion H; subst; clear H
    | [H : ( _ :: _ ) = ( _ :: _ )  |- _ ] => inversion H; subst; clear H
  end.
