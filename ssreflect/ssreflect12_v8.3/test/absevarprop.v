Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.

Definition P := fun x : nat => x < 3.
Definition Q := fun (x : nat) (p : P x) => x > 0.
Definition R := fun (x : nat) (p : P x) m (q : P (x+1)) => m > 0.

Inductive myEx : Type := ExI : forall n (pn : P n) pn', Q n pn -> R n pn n pn' -> myEx.

Lemma testmE1 : myEx.
Proof.
apply: ExI 1 _ _ _ _.
  match goal with |- is_true (P 1) => done | _ => fail end.
  match goal with |- is_true (P (1+1)) => done | _ => fail end.
  match goal with |- forall p : is_true (P 1), is_true (Q 1 p) => done | _ => fail end.
match goal with |- 
forall (p : is_true (P 1)) (q : is_true (P (1+1))), is_true (R 1 p 1 q) => done | _ => fail end.
Qed.

Lemma testE2 : exists y : { x | P x }, sval y = 1.
Proof.
apply: ex_intro (exist _ 1 _) _.
  match goal with |- is_true (P 1) => done | _ => fail end.
match goal with 
|- forall p : is_true (P 1), @sval _ _ (@exist _ _ 1 p) = 1 => done | _ => fail end.
Qed.

Lemma testE3 : exists y : { x | P x }, sval y = 1.
Proof.
have := (ex_intro _ (exist _ 1 _) _); apply.
  match goal with |- is_true (P 1) => done | _ => fail end.
match goal with 
|- forall p : is_true (P 1), @sval _ _ (@exist _ _ 1 p) = 1 => done | _ => fail end.
Qed.
