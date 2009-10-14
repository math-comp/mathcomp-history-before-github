Require Export Setoid.
Add LoadPath "../../../".
Require Import ssreflect.


Lemma L (T: Type) (R: relation T) (E: Equivalence R) (x y: T)
   (H: R x y): R y x.
   intros.
   rewrite H. (* error: not a rewritable relation: (R x y) in rule H *)
Admitted.
