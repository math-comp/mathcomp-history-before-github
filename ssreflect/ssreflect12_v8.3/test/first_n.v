Require Import ssreflect ssrbool.

Lemma test : False -> (bool -> False -> True -> True) -> True.
move=> F; let w := 2 in apply; last w first.
- by apply: F.
- by apply: I.
by apply: true.
Qed.