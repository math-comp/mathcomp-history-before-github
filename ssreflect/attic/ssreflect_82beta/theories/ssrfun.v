(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Delimit Scope fun_scope with FUN.
Open Scope fun_scope.

(* Basic constructions for intuitionistic functions : extensional equality   *)
(* composition, override, update, inverse, and iteration, with some their    *)
(* identities, and reflected equalities.                                     *)

(* Miscellaneous notation bits for currrying and pairs *)

Notation "f ^~ y" := (fun x => f x y)
  (at level 10, y at level 8, no associativity, format "f ^~  y") : fun_scope.

Delimit Scope pair_scope with PAIR.
Open Scope pair_scope.

Notation "p .1" := (fst p) (at level 2, left associativity,
  format "p .1") : pair_scope.
Notation "p .2" := (snd p) (at level 2, left associativity,
  format "p .2") : pair_scope.

(* Complements on the option type constructor, used below to  *)
(* encode partial functions.                                  *)

Module Option.

Definition apply aT rT (f : aT -> rT) x u := if u is Some y then f y else x.

Definition default T := apply (fun x : T => x).

Definition bind aT rT (f : aT -> option rT) := apply f None.

Definition map aT rT (f : aT -> rT) := bind (fun x => Some (f x)).

End Option.

Notation oapp := Option.apply.
Notation odflt := Option.default.
Notation obind := Option.bind.
Notation omap := Option.map.
Notation some := (@Some _) (only parsing).

(* Reserved Notation "- 1" (at level 35). *)
Reserved Notation "x ^-1" (at level 2, left associativity, format "x ^-1").
Reserved Notation "x ^2" (at level 2, left associativity, format "x ^2").

(* Syntax for defining auxiliary recursive function.          *)
(*  Usage:                                                    *)
(* Section FooDefinition.                                     *)
(* Variables (g1 : T1) (g2 : T2).  (globals)                  *)
(* Fixoint foo_auxiliary (a3 : T3) ... :=                     *)
(*        body, using [rec e3, ...] for recursive calls       *)
(* where "[ 'rec' a3 , a4 , ... ]" := foo_auxiliary.          *)
(* Definition foo x y .. := [rec e1, ...].                    *)
(* + proofs about foo                                         *)
(* End FooDefinition.                                         *)

Reserved Notation "[ 'rec' a0 ]"
  (at level 0).
Reserved Notation "[ 'rec' a0 , a1 ]"
  (at level 0).
Reserved Notation "[ 'rec' a0 , a1 , a2 ]"
  (at level 0).
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 ]"
  (at level 0).
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 ]"
  (at level 0).
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 ]"
  (at level 0).
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 , a6 , a7 ]"
  (at level 0).
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 , a6 , a7 , a8 ]"
  (at level 0).
Reserved Notation "[ 'rec' a0 , a1 , a2 , a3 , a4 , a5 , a6 , a7 , a8 , a9 ]"
  (at level 0).

(* Definitions and notation for explicit functions with simplification,     *)
(* i.e., which simpl and /= beta expand (this is complementary to nosimpl). *)

Section SimplFun.

Variables aT rT : Type.

CoInductive simpl_fun : Type := SimplFun of aT -> rT.

Definition fun_of_simpl := fun f x => let: SimplFun lam := f in lam x.

Coercion fun_of_simpl : simpl_fun >-> Funclass.

End SimplFun.

Notation "[ 'fun' : T => E ]" := (SimplFun (fun _ : T => E))
  (at level 0,
   format "'[hv' [ 'fun' :  T  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x => E ]" := (SimplFun (fun x => E))
  (at level 0, x ident,
   format "'[hv' [ 'fun'  x  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x : T => E ]" := (SimplFun (fun x : T => E))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'fun' x y => E ]" := (fun x => [fun y => E])
  (at level 0, x ident, y ident,
   format "'[hv' [ 'fun'  x  y  => '/ '  E ] ']'") : fun_scope.

Notation "[ 'fun' x y : T => E ]" := (fun x : T => [fun y : T => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' ( x : T ) y => E ]" := (fun x : T => [fun y => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' x ( y : T ) => E ]" := (fun x => [fun y : T => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

Notation "[ 'fun' ( x : xT ) ( y : yT ) => E ]" :=
    (fun x : xT => [fun y : yT => E])
  (at level 0, x ident, y ident, only parsing) : fun_scope.

(* For delta functions in eqtype.v. *)
Definition SimplFunDelta aT rT (f : aT -> aT -> rT) := [fun z => f z z].

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

Lemma ftrans : forall f g (h:B -> A), eqfun f g -> eqfun g h -> eqfun f h.
Proof. by move=> f g h Hfg Hgh x; rewrite (Hfg x). Qed.

Lemma rrefl : forall f, eqrel f f. Proof. split. Qed.

End ExtensionalEquality.

Hint Resolve frefl rrefl.

Notation "f1 =1 f2" := (eqfun f1 f2)
  (at level 70, no associativity) : fun_scope.
Notation "f1 =1 f2 :> A" := (f1 =1 (f2 : A))
  (at level 70, f2 at next level, A at level 90) : fun_scope.
Notation "f1 =2 f2" := (eqrel f1 f2)
  (at level 70, no associativity) : fun_scope.
Notation "f1 =2 f2 :> A" := (f1 =2 (f2 : A))
  (at level 70, f2 at next level, A, B at level 90) : fun_scope.

Section Composition.

Variables A B C : Type.

Definition comp (f : B -> A) (g : C -> B) := [fun x => f (g x)].

Definition pcomp (f : B -> option A) (g : C -> option B) x := obind f (g x).

Lemma eq_comp : forall f f' g g', f =1 f' -> g =1 g' -> comp f g =1 comp f' g'.
Proof. by move=> f f' g g' Ef Eg x; rewrite /= Eg Ef. Qed.

End Composition.

Notation "[ 'eta' f ]" := (fun x => f x)
  (at level 0, format "[ 'eta'  f ]") : fun_scope.

Notation id := (fun x => x).
Notation "@ 'id' T " := (fun x : T => x)
  (at level 10, T at level 8, only parsing) : fun_scope.

Notation "f1 \o f2" := (fun_of_simpl (comp f1 f2))
  (at level 50) : fun_scope.

Section OperationProperties.

Variable T : Type.
Variables zero one: T.
Variable inv : T -> T.
Variables mul add : T -> T -> T.

Notation Local "1" := one.
Notation Local "0" := zero.
Notation Local "x ^-1" := (inv x).
Notation Local "x * y"  := (mul x y).
Notation Local "x + y"  := (add x y).

Definition left_unit          := forall x,     1 * x = x.
Definition right_unit         := forall x,     x * 1 = x.
Definition left_inverse       := forall x,     x^-1 * x = 1.
Definition right_inverse      := forall x,     x * x^-1 = 1.
Definition self_inverse       := forall x,     x * x = 1.
Definition idempotent         := forall x,     x * x = x.
Definition associative        := forall x y z, x * (y * z) = x * y * z.
Definition commutative        := forall x y,   x * y = y * x.
Definition left_commutative   := forall x y z, x * (y * z) = y * (x * z).
Definition right_commutative  := forall x y z, x * y * z = x * z * y.
Definition left_zero          := forall x,     0 * x = 0.
Definition right_zero         := forall x,     x * 0 = 0.
Definition left_distributive  := forall x y z, (x + y) * z = x * z + y * z.
Definition right_distributive := forall x y z, x * (y + z) = x * y + x * z.

End OperationProperties.

Section Morphism.

Variables (aT rT sT : Type) (f : aT -> rT).

Definition morphism_1 aF rF := forall x, f (aF x) = rF (f x).
Definition morphism_2 aOp rOp := forall x y, f (aOp x y) = rOp (f x) (f y).

End Morphism.

Notation "{ 'morph' f : x / a >-> r }" :=
  (morphism_1 f (fun x => a) (fun x => r))
  (at level 0, f at level 99, x ident,
   format "{ 'morph'  f  :  x  /  a  >->  r }") : type_scope.

Notation "{ 'morph' f : x / a }" :=
  (morphism_1 f (fun x => a) (fun x => a))
  (at level 0, f at level 99, x ident,
   format "{ 'morph'  f  :  x  /  a }") : type_scope.

Notation "{ 'morph' f : x y / a >-> r }" :=
  (morphism_2 f (fun x y => a) (fun x y => r))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'morph'  f  :  x  y  /  a  >->  r }") : type_scope.

Notation "{ 'morph' f : x y / a }" :=
  (morphism_2 f (fun x y => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'morph'  f  :  x  y  /  a }") : type_scope.

(* In an intuitionistic setting, we have two degrees of injectivity. The     *)
(* weaker one gives only simplification, and the strong one provides a left  *)
(* inverse (we show in `fintype' that they coincide for finite types).       *)
(* We also define an intermediate version where the left inverse is only a   *)
(* partial function.                                                         *)

Section Injections.

(* rT must come first so we can use @ to mitigate the Coq 1st order   *)
(* unification bug (e..g., Coq can't infer rT from a "cancel" lemma). *)
Variables (rT aT : Type) (f : aT -> rT).

Definition injective := forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition cancel g := forall x, g (f x) = x.

Definition pcancel g := forall x, g (f x) = Some x.

Definition ocancel (g : aT -> option rT) h := forall x, oapp h x (g x) = x.

Lemma can_pcan : forall g, cancel g -> pcancel (fun y => Some (g y)).
Proof. by move=> g fK x; congr (Some _). Qed.

Lemma pcan_inj : forall g, pcancel g -> injective.
Proof. by move=> g fK x y; move/(congr1 g); rewrite !fK => [[]]. Qed.

Lemma can_inj : forall g, cancel g -> injective.
Proof. by move=> g; move/can_pcan; exact: pcan_inj. Qed.

Lemma canLR : forall g x y, cancel g -> x = f y -> g x = y.
Proof. by move=> g x y fK ->. Qed.

Lemma canRL : forall g x y, cancel g -> f x = y -> x = g y.
Proof. by move=> g x y fK <-. Qed.

End Injections.

Section InjectionsTheory.

Variables (A B C : Type) (f f' : B -> A) (g g' : A -> B).
Variables (h : C -> B) (k : B -> C).
Hypotheses (Hf : injective f) (Hfg : cancel f g) (Hg : injective g).
Hypotheses (Hh : injective h) (Hhk : cancel h k).

Lemma inj_can_sym : cancel g f.
Proof. move=> x; exact: Hg. Qed.

Lemma inj_comp : injective (f \o h).
Proof. move=> x y; move/Hf; exact: Hh. Qed.

Lemma inj_id : injective (@id A).
Proof. by []. Qed.

Lemma can_comp : cancel (f \o h) (k \o g).
Proof. by move=> x; rewrite /= Hfg Hhk. Qed.

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
move=> [h Ef Eh] [k Eg Ek]; exists (k \o h : _ -> _); apply can_comp; auto.
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








