(* (c) Copyright Microsoft Corporation and Inria. You may distribute   *)
(* under the terms of either the CeCILL-B License or the CeCILL        *)
(* version 2 License, as specified in the README file.                 *)
Require Import ssreflect.

(****************************************************************************)
(* This file contains the basic definitions and notations for working with  *)
(* functions. The definitions concern:                                      *)
(*                                                                          *)
(*  Pair projections                                                        *)
(*    p.1  == first element of a pair                                       *)
(*    p.2  == second element of a pair                                      *)
(*                                                                          *)
(*  Simplifying functions, beta-reduced by simpl and /= :                   *)
(*           [fun : T => E] == constant function from type T that returns E *)
(*             [fun x => E] == unary function                               *)
(*         [fun x : T => E] == unary function with explicit domain type     *)
(*           [fun x y => E] == binary function                              *)
(*       [fun x y : T => E] == binary function with explicit domain type    *)
(*     [fun (x : T) y => E] == binary function with explicit domain type    *)
(*     [fun x (y : T) => E] == binary function with explicit domain type    *)
(*    [fun (x : xT) (y : yT) => E]                                          *)
(*                                                                          *)
(* - partial functions using option type,                                   *)
(*     oapp f d ox == if ox is Some x returns f x,        d otherwise       *)
(*      odflt d ox == if ox is Some x returns x,          d otherwise       *)
(*      obind f ox == if ox is Some x returns f x,        None otherwise    *)
(*       omap f ox == if ox is Some x returns Some (f x), None otherwise    *)
(*                                                                          *)
(* - extensional equality for functions and relations (i.e. functions of 2  *)
(*   arguments),                                                            *)
(*    f1 =1 f2      ==  f1 x is equal to f2 x forall x                      *)
(*    f1 =1 f2 :>A  ==    ... and f2 is explicitly typed                    *)
(*    f1 =2 f2      ==  f1 x y is equal to f2 x y forall x y                *)
(*    f1 =2 f2 :> A ==    ... and f2 is explicitly typed                    *)
(*                                                                          *)
(* - composition for total and partial functions,                           *)
(*             f^~y == function f with y as second argument y               *)
(*        f1 \o f2  == composition of f1 and f2                             *)
(*      pcomp f1 f2 == composition of partial functions f1 and f2           *)
(*                                                                          *)
(* - properties of functions                                                *)
(*        injective f == f is injective                                     *)
(*         cancel f g == g is the inverse of f                              *)
(*        pcancel f g == g is the inverse of f where g is partial           *)
(*        ocancel f g == g is the inverse of f where f is partial           *)
(*        bijective f == f is bijective                                     *)
(*       involutive f == f is involutive                                    *)
(*                                                                          *)
(* - properties for operations                                              *)
(*                left_id e op == e is a left identity for op               *)
(*               right_id e op == e is a right identity for op              *)
(*         left_inverse e i op == i is a left inverse for op with unit e    *)
(*        right_inverse e i op == i is a right inverse for op with unit e   *)
(*         self_inverse x e op == x is its own inverse for op               *)
(*             idempotent x op == x is idempotent                           *)
(*                associate op == op is associative                         *)
(*              commutative op == op is commutative                         *)
(*         left_commutative op == op is left commutative                    *)
(*        right_commutative op == op is right commutative                   *)
(*              left_zero z op == z is a right zero for op                  *)
(*             right_zero z op == z is a right zero for op                  *)
(*   left_distributive op1 op2 == op1 is left distributive for op2          *)
(*  right_distributive op1 op2 == op1 is right distributive for op2         *)
(*                                                                          *)
(* - morphisms for functions and relations,                                 *)
(*  {morph f : x / a >-> r } == f is a morphism with respect to functions   *)
(*                                 (fun x => a) and (fun x => r)            *)
(*  {morph f : x / a } == f is a morphism with respect to (fun x => a)      *)
(*  {morph f : x y / a >-> r } == f is a morphism with respect to functions *)
(*                                 (fun x y => a) and (fun x y => r)        *)
(*  {morph f : x / a } == f is a morphism with respect to (fun x y => a)    *)
(*                                                                          *)
(* The file also contains some basic lemmas for the above concepts.         *)
(****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Delimit Scope fun_scope with FUN.
Open Scope fun_scope.

Notation "f ^~ y" := (fun x => f x y)
  (at level 10, y at level 8, no associativity, format "f ^~  y") : fun_scope.

Delimit Scope pair_scope with PAIR.
Open Scope pair_scope.

(* Notations for pair projections *)
Notation "p .1" := (fst p)
  (at level 2, left associativity, format "p .1") : pair_scope.
Notation "p .2" := (snd p)
  (at level 2, left associativity, format "p .2") : pair_scope.

(* Reserved notations for evaluation *)
Reserved Notation "e .[ x ]"
  (at level 2, left associativity, format "e .[ x ]").

Reserved Notation "e .[ x1 , x2 , .. , xn ]"
  (at level 2, left associativity,
   format "e '[ ' .[ x1 , '/'  x2 , '/'  .. , '/'  xn ] ']'").

(* Reserved notations for subscripting and superscripting *)
Reserved Notation "x ^-1"
  (at level 3, left associativity, format "x ^-1").

Reserved Notation "x *+ n" (at level 40, left associativity).
Reserved Notation "x *- n" (at level 40, left associativity).
Reserved Notation "x ^+ n" (at level 29, left associativity).
Reserved Notation "x ^- n" (at level 29, left associativity).

Reserved Notation "s `_ i"
  (at level 3, i at level 2, left associativity, format "s `_ i").

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

(* Shorthand for some basic equality lemmas. *)

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

Definition eqrel (r s : C -> B -> A) : Prop := forall x y, r x y = s x y.

Lemma frefl : forall f, eqfun f f. Proof. by []. Qed.
Lemma fsym : forall f g, eqfun f g -> eqfun g f. Proof. by move=> f g E x. Qed.

Lemma ftrans : forall f g h, eqfun f g -> eqfun g h -> eqfun f h.
Proof. by move=> f g h eqfg eqgh x; rewrite eqfg. Qed.

Lemma rrefl : forall r, eqrel r r. Proof. by []. Qed.

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

Notation "f1 \o f2" := (comp f1 f2) (at level 50) : fun_scope.

Definition idfun T := @id T.
Prenex Implicits idfun.

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

Definition left_id          := forall x,     1 * x = x.
Definition right_id         := forall x,     x * 1 = x.
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

Variables (A B C : Type) (f g : B -> A) (h : C -> B).

Lemma inj_id : injective (@id A).
Proof. by []. Qed.

Lemma inj_can_sym : forall f', cancel f f' -> injective f' -> cancel f' f.
Proof. move=> f' fK injf' x; exact: injf'. Qed.

Lemma inj_comp : injective f -> injective h -> injective (f \o h).
Proof. move=> injf injh x y; move/injf; exact: injh. Qed.

Lemma can_comp : forall f' h',
  cancel f f' -> cancel h h' -> cancel (f \o h) (h' \o f').
Proof. by move=> f' h' fK hK x; rewrite /= fK hK. Qed.

Lemma pcan_pcomp : forall f' h',
  pcancel f f' -> pcancel h h' -> pcancel (f \o h) (pcomp h' f').
Proof. by move=> f' h' fK hK x; rewrite /pcomp fK /= hK. Qed.

Lemma eq_inj : injective f -> f =1 g -> injective g.
Proof. by move=> injf eqfg x y; rewrite -2!eqfg; exact: injf. Qed.

Lemma eq_can : forall f' g', cancel f f' -> f =1 g -> f' =1 g' -> cancel g g'.
Proof. by move=> f' g' fK eqfg eqfg' x; rewrite -eqfg -eqfg'. Qed.

Lemma inj_can_eq : forall f',
  cancel f f' -> injective f' -> cancel g f' -> f =1 g.
Proof. by move=> f' fK injf' gK x; apply: injf'; rewrite fK. Qed.

End InjectionsTheory.

Section Bijections.

Variables (A B : Type) (f : B -> A).

Definition bijective : Prop := exists2 g, cancel f g & cancel g f.

Hypothesis bijf : bijective.

Lemma bij_inj : injective f.
Proof. by case: bijf => [h fK _]; apply: can_inj fK. Qed.

Lemma bij_can_sym : forall f', cancel f' f <-> cancel f f'.
Proof.
move=> f'; split=> fK; first exact: inj_can_sym fK bij_inj.
by case: bijf => [h _ hK] x; rewrite -[x]hK fK.
Qed.

Lemma bij_can_eq : forall f' f'', cancel f f' -> cancel f f'' -> f' =1 f''.
Proof.
by move=> f' f'' fK fK'; apply: (inj_can_eq _ bij_inj); apply/bij_can_sym.
Qed.

End Bijections.

Section BijectionsTheory.

Variables (A B C : Type) (f : B -> A) (h : C -> B).

Lemma eq_bij : bijective f -> forall g, f =1 g -> bijective g.
Proof. by move=> [f' fK f'K] g eqfg; exists f'; eapply eq_can; eauto. Qed.

Lemma bij_comp : bijective f -> bijective h -> bijective (f \o h).
Proof.
move=> [f' fK f'K] [h' hK h'K].
by exists (h' \o f' : _ -> _); apply can_comp; auto.
Qed.

Lemma bij_can_bij : bijective f -> forall f', cancel f f' -> bijective f'.
Proof. by move=> bijf; exists f; first by apply/(bij_can_sym bijf). Qed.

End BijectionsTheory.

Section Involutions.

Variables (A : Type) (f : A -> A).

Definition involutive := cancel f f.

Hypothesis Hf : involutive.

Lemma inv_inj : injective f. Proof. exact: can_inj Hf. Qed.
Lemma inv_bij : bijective f. Proof. by exists f. Qed.

End Involutions.








