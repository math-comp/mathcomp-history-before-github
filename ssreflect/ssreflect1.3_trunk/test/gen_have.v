Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set SsrDebug.
Axiom P : nat -> Prop.

Lemma test1 n (ngt0 : 0 < n) : P n.
gen have lt2le, /andP[H1 H2] : n ngt0 / (0 <= n) && (n != 0).
  match goal with |- is_true((0 <= n) && (n != 0)) => admit end.
Check (lt2le : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
Check (H1 : 0 <= n).
Check (H2 : n != 0).
admit.
Qed.

Lemma test2 n (ngt0 : 0 < n) : P n.
gen have _, /andP[H1 H2] : n ngt0 / (0 <= n) && (n != 0).
  match goal with |- is_true((0 <= n) && (n != 0)) => admit end.
lazymatch goal with
 | lt2le : forall n : nat, is_true(0 < n) -> is_true((0 <= n) && (n != 0))
    |- _ => fail "not cleared"
 | _ => idtac end.
Check (H1 : 0 <= n).
Check (H2 : n != 0).
admit.
Qed.

Lemma test3 n (ngt0 : 0 < n) : P n.
gen have H : n ngt0 / (0 <= n) && (n != 0).
  match goal with |- is_true((0 <= n) && (n != 0)) => admit end.
Check (H : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
admit.
Qed.

Lemma test4 n (ngt0 : 0 < n) : P n.
gen have : n ngt0 / (0 <= n) && (n != 0).
  match goal with |- is_true((0 <= n) && (n != 0)) => admit end.
move=> H.
Check(H : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
admit.
Qed.

Lemma test4bis n (ngt0 : 0 < n) : P n.
wlog suff : n ngt0 / (0 <= n) && (n != 0); last first.
  match goal with |- is_true((0 <= n) && (n != 0)) => admit end.
move=> H.
Check(H : forall n : nat, 0 < n -> (0 <= n) && (n != 0)).
admit.
Qed.

Lemma test5 n (ngt0 : 0 < n) : P n.
Fail gen have : / (0 <= n) && (n != 0).
Abort.

Lemma test6 n (ngt0 : 0 < n) : P n.
gen have : n ngt0 / (0 <= n) && (n != 0) by admit.
Abort.

Lemma test7 n (ngt0 : 0 < n) : P n.
Fail gen have : n / (0 <= n) && (n != 0).
Abort.





(*
Goal forall n, n >= 0 -> True.
move=> n.
elim E : 0 => [|m IHm].
  admit.yes


Notation "( x := t )" := t ().
*)

generally have P , ipat : hyps / type
  have ipat : type
  have P : forall hyps, type
  assert hyps <> []

wlog H : hyps (new_x := old_t) / typegit remote 
  
   =====
   (forall new_x, type -> G[old_t -> new_x]) -> G

new_x
H : type
====
G[old_t -> new_x]


-------------------------------------------
move: t => x; move: x.
move: (x := t).

====
forall x, G[t -> x]
---------------------------
elim E : t.




