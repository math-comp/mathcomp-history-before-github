Require Import ssreflect.

Variable T : Type.
Variables P : T -> Prop.

Definition f := fun x y : T => x.

Lemma test1 : forall x y : T, P (f x y) -> P x.
Proof.
move=> x y; set fxy := f x y; move=> Pfxy.
wlog H : fxy Pfxy / P x.
  match goal with |- (let fxy0 := f x y in P fxy0 -> P x -> P x) -> P x => by auto | _ => fail end.
exact: H.
Qed.
