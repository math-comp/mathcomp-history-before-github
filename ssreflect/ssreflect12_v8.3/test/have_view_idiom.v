Require Import ssreflect ssrbool.

Lemma test (a b : bool) (pab : a && b) : b.
have {pab} /= /andP [pa -> //] /= : true && (a && b) := pab.
Qed.
