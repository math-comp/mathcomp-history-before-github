Require Import ssreflect ssrbool eqtype ssrnat.

Lemma test1 : forall a b : nat, a == b -> a == 0 -> b == 0.
move=> a b Eab Eac; congr (_ == 0) : Eac; exact: eqP Eab.
Qed.

Variable S : eqType.
Variable f : nat -> S.
Coercion f : nat >-> Equality.sort.

Lemma test2 : forall a b : nat, b = a -> @eq S (b + b) (a + a).
move=> a b Eba; congr (_ + _); exact:  Eba. 
Qed.