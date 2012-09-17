(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module BigEnough.

Definition leq_maxE := (orTb, orbT, leqnn, leq_max).

Fixpoint bigger_than s := if s is a :: r then maxn a (bigger_than r) else 0%N.

Definition closed T (i : T) := {j : T | j = i}.
Ltac close :=  match goal with
                 | |- context [closed ?i] =>
                   instantiate (1 := [::]) in (Value of i); exists i
               end.

Ltac pose_big_enough i :=
  evar (i : nat); suff : closed i; first do
    [move=> _; instantiate (1 := bigger_than _) in (Value of i)].

Ltac pose_big_modulus m F :=
  evar (m : F -> nat); suff : closed m; first do
    [move=> _; instantiate (1 := (fun e => bigger_than _)) in (Value of m)].

Ltac exists_big_modulus m F := pose_big_modulus m F; first exists m.

Definition selected := locked.
Lemma select T (x : T) : x = selected x. Proof. exact: lock. Qed.

Lemma instantiate_bigger_than (P : bool -> Type) i s :
  P true -> P ((i <= selected bigger_than (i :: s))%N).
Proof. by rewrite -select ?leq_maxE. Qed.

Ltac big_selected i :=
  rewrite ?[in X in selected X]/i;
  rewrite ?[in X in selected X]leq_max -/bigger_than;
  rewrite [bigger_than in X in selected X]select;
  apply instantiate_bigger_than;
  rewrite ?[in X in selected X]orbA;
  rewrite 1?[in X in selected X]orbT;
  rewrite -?select.

Ltac big1 :=
  match goal with
    | |- context [(?x <= ?i)%N] => rewrite [(x <= i)%N]select; big_selected i
  end.

Ltac big :=
  match goal with
        | leq_mi : is_true (?m <= ?i)%N |- context [(?x <= ?i)%N] =>
            rewrite [(x <= i)%N](leq_trans _ leq_mi) /=; last by big1
        | _ => big1
  end.

End BigEnough.

(*
If I do: 

Ltac big :=
  do [ match goal with
         | leq_mi : is_true (?m <= ?i)%N |- context [(?x <= ?i)%N] =>
              rewrite [(x <= i)%N](leq_trans _ leq_mi) /=; last by big1
         | _ => big1
       end
     | fail "The big tactic failed (because of circular dependency ?)"].

When big is invoked, I get:

 Toplevel input, characters 30-33:
Anomaly: File "tactics/tacinterp.ml", line 1782, characters 35-41: Assertion failed.
Please report.

*)