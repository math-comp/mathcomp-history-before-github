Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.


Lemma test1 n : n >= 0.
Proof.
have {&s} @h m : 'I_(n+m).+1.
  apply: Sub 0 _.
  hide: s m.
  by auto.
Show Proof.
cut (forall m, 0 < (n+m).+1); last assumption.
by [].
Qed.

(*
2 subgoals
n : nat
s : <skolem 5 >
m : nat
______________________________________(1/2)
'I_(n + m).+1
______________________________________(2/2)
0 <= n



2 subgoals
n : nat
m : nat
______________________________________(1/2)
0 < (n + m).+1
______________________________________(2/2)
0 <= n


1 subgoal
n : nat
s : (forall m : nat, 0 < (n + m).+1)
h := fun m : nat => Sub 0 (s m)
  : forall m : nat, 'I_(n + m).+1
______________________________________(1/1)
0 <= n
*)