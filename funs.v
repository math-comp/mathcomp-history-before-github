(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Delimit Scope fun_scope with FUN.
Open Scope fun_scope.

(* Basic constructions for intuitionistic functions : extensional equality   *)
(* composition, override, update, inverse, and iteration, with some their    *)
(* identities, and reflected equalities.                                     *)

(* Shorthand for some basic equality lemmas lemmas. *)

Definition erefl := refl_equal.
Definition esym := sym_eq.
Definition nesym := sym_not_eq.
Definition etrans := trans_eq.
Definition congr1 := f_equal.
Definition congr2 := f_equal2.
(* Force at least one implicit when used as a view. *)
Prenex Implicits esym nesym.

(* Extensional equality, for unary and binary functions, including syntactic *)
(* sugar.                                                                    *)

Section ExtensionalEquality.

Variables A B C : Type.

Definition eqfun (f g : B -> A) : Prop := forall x, f x = g x.

Definition eqrel (f g : C -> B -> A) : Prop := forall x y, f x y = g x y.

Lemma frefl : forall f, eqfun f f. Proof. split. Qed.
Lemma fsym : forall f g, eqfun f g -> eqfun g f. Proof. move=> f g H x; auto. Qed.
Lemma rrefl : forall f, eqrel f f. Proof. split. Qed.

End ExtensionalEquality.

Hint Resolve frefl rrefl.

Notation "f1 '=1' f2" := (eqfun f1 f2)
  (at level 70, no associativity) : fun_scope.
Notation "f1 '=1' f2 ':>' A" := (f1 =1 (f2 : A))
  (at level 70, f2 at next level, A at level 90) : fun_scope.
Notation "f1 '=2' f2" := (eqrel f1 f2)
  (at level 70, no associativity) : fun_scope.
Notation "f1 '=2' f2 ':>' A " := (f1 =2 (f2 : A))
  (at level 70, f2 at next level, A, B at level 90) : fun_scope.

Section Composition.

Variables A B C : Type.

Definition id (x : A) := x.

Definition comp (f : B -> A) (g : C -> B) x := f (g x).

Lemma eq_comp : forall f f' g g', f =1 f' -> g =1 g' -> comp f g =1 comp f' g'.
Proof. by move=> f f' g g' Ef Eg x; rewrite /comp Eg Ef. Qed.

End Composition.

Prenex Implicits id.

Notation "f1 \o f2" := (comp f1 f2)  (at level 50) : fun_scope.

(* Simple iteration (`for' loops!), indexed and unindexed.                  *)

Section Iteration.

Variable A : Type.

Definition iter_n n f x :=
  let fix loop (m : nat) : A := if m is S i then f i (loop i) else x in loop n.

Definition iter n f x :=
  let fix loop (m : nat) : A := if m is S i then f (loop i) else x in loop n.

Lemma iter_f : forall n f x, iter n f (f x) = iter (S n) f x.
Proof. by move=> n f x; elim: n => [|n Hrec] //; congr f. Qed.

Lemma f_iter : forall n f x, f (iter n f x) = iter (S n) f x.
Proof. done. Qed.

Lemma eq_iter : forall f f', f =1 f' -> forall n, iter n f =1 iter n f'.
Proof. by move=> f f' Ef n; elim: n => [|n Hrec] x //=; rewrite Ef Hrec. Qed.

Lemma eq_iter_n : forall f f', f =2 f' -> forall n, iter_n n f =1 iter_n n f'.
Proof. by move=> f f' Ef; elim=> [|n Hrec] x //=; rewrite Ef Hrec. Qed.

End Iteration.

(* In an intuitionistic setting, we have two degrees of injectivity. The     *)
(* weaker one gives only simplification, and the strong one provides a left  *)
(* inverse (we show in `fintype' that they coincide for finite types).        *)
(* (The definition could be further weakened if equality on A is not         *)
(* decidable, to ~ x = y -> ~ (f x) = (f y), but this doesn't seem useful.)  *)

Section Injections.

Variables (A B : Type) (f : B -> A) (g : A -> B).

Definition injective : Prop := forall x x' : B, f x = f x' -> x = x'.

Definition cancel : Prop := forall x, g (f x) = x.

Lemma canLR : forall x y, x = f y -> cancel -> g x = y.
Proof. by move=> x y ->. Qed.

Lemma canRL : forall x y, f x = y -> cancel -> x = g y.
Proof. by move=> x y <-. Qed.

Lemma can_inj : cancel -> injective.
Proof. by move=> Hf x y Ef; rewrite -[x]Hf Ef. Qed.

End Injections.

Section InjectionsTheory.

Variables (A B C : Type) (f f' : B -> A) (g g' : A -> B).
Variables (h : C -> B) (k : B -> C).
Hypotheses (Hf : injective f) (Hfg : cancel f g) (Hg : injective g).
Hypotheses (Hh : injective h) (Hhk : cancel h k).

Lemma inj_can_sym : cancel g f. Proof. move=> x; exact: Hg. Qed.

Lemma inj_comp : injective (f \o h). Proof. move=> x y; move/Hf; exact: Hh. Qed.

Lemma can_comp : cancel (f \o h) (k \o g).
Proof. by move=> x; rewrite /comp Hfg Hhk. Qed.

Lemma eq_inj : f =1 f' -> injective f'.
Proof. move=> Ef x y; rewrite -2!Ef; exact: Hf. Qed.

Lemma eq_can : f =1 f' -> g =1 g' -> cancel f' g'.
Proof. by move=> Ef Eg x; rewrite -Ef -Eg. Qed.

Lemma inj_can_eq : cancel f' g -> f =1 f'.
Proof. by move=> Hf'g x; apply: Hg; rewrite Hfg. Qed.

End InjectionsTheory.

Section Bijections.

Variables (A B : Type) (f : B -> A).

Definition bijective : Prop := exists2 g, cancel f g & cancel g f.

Hypothesis Hf : bijective.

Lemma bij_inj : injective f.
Proof. by case: Hf => [h Ef _]; apply: can_inj Ef. Qed.

Lemma bij_can_sym : forall g, cancel g f <-> cancel f g.
Proof.
move=> g; split=> Eg; first exact: inj_can_sym Eg bij_inj.
by case: Hf => [h _ Eh] x; rewrite -[x]Eh Eg.
Qed.

Lemma bij_can_eq : forall g g', cancel f g -> cancel f g' -> g =1 g'.
Proof.
by move=> g g' Eg Eg'; apply: (inj_can_eq _ bij_inj); apply/bij_can_sym.
Qed.

End Bijections.

Section BijectionsTheory.

Variables (A B C : Type) (f : B -> A) (g : C -> B).

Lemma eq_bij : bijective f -> forall f', f =1 f' -> bijective f'.
Proof. by move=> [h Ef Eh] f' Eff'; exists h; eapply eq_can; eauto. Qed.

Lemma bij_comp : bijective f -> bijective g -> bijective (f \o g).
Proof.
move=> [h Ef Eh] [k Eg Ek]; exists (comp k h); apply can_comp; auto.
Qed.

Lemma bij_can_bij :
  bijective f -> forall h, cancel f h -> bijective h.
Proof. by move=> Hf; exists f; first by apply/(bij_can_sym Hf). Qed.

End BijectionsTheory.

Section Involutions.

Variables (A : Type) (f : A -> A).

Definition involutive := cancel f f.

Hypothesis Hf : involutive.

Lemma inv_inj : injective f. Proof. exact: can_inj Hf. Qed.
Lemma inv_bij : bijective f. Proof. by exists f. Qed.

End Involutions.

Unset Implicit Arguments.








