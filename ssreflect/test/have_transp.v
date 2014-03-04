Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.


Lemma test1 (n : nat) : False.
Proof.
have @a : 'I_n.+1 by apply (Sub 0); hide; auto.

Show Proof.

have @b : 'I_n.+1 by apply (Sub 0); hide as fooo; auto.

have helper_4_auto x : O < n + x.+1 by rewrite addnS.
have @h x y (w := x + y) z : 'I_(n + (z+w).+1)
  by apply (Sub O); hide as blurb; auto.



Admitted.
