(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Generic definitions and lemmas for datatypes with reflected (decidable) *)
(* equality. The structure includes the actual boolean predicate, not just *)
(* the decision procedure. A canonical structure for the booleans is given *)
(* here, and one will be provided for the integers in ssrnat.v.            *)
(*   The syntax {t as eqType} denotes the canonical eqType structure on a  *)
(* type t (up to conversion). This provides a way of directly looking up   *)
(* a canonical structure.                                                  *)
(*   Congruence properties of injective functions wrt reflected equality   *)
(* are established.                                                        *)
(*   Basic definitions are also given for sets and relations (i.e., unary  *)
(* and binary boolean predicates); however, the boolean algebra is NOT     *)
(* lifted to sets.                                                         *)
(*   The main technical result is the construction of the subdomain        *)
(* associated with a set.                                                  *)
(*   Syntactic sugar is provided for the equality predicate and its        *)
(* reflection property.                                                    *)

Definition reflect_eq d eq :=
  forall x y : d, reflect (x = y) (eq x y).

Module EqType.

Structure eqType : Type :=
  EqType {sort :> Type; eq : sort -> sort -> bool; eqP : reflect_eq eq}.

End EqType.

Delimit Scope eq_scope with EQ.
Open Scope eq_scope.

Notation eqType := EqType.eqType.
Notation EqType := EqType.EqType.

Definition set1 := nosimpl EqType.eq.

Lemma set1E : set1 = EqType.eq. Proof. done. Qed.

Prenex Implicits set1.

Notation "x '==' y" := (set1 x y)
  (at level 70) : eq_scope.
Notation "x '==' y ':>' d" := (set1 (x : d) (y : d))
  (at level 70, y at next level) : eq_scope.
Notation "x '!=' y" := (~~ (x == y))
  (at level 70) : eq_scope.
Notation "x '!=' y ':>' d" := (~~ (x == y :> d))
  (at level 70, y at next level) : eq_scope.

Lemma set1P : forall (d : eqType) (x y : d), reflect (x = y) (x == y).
Proof. exact EqType.eqP. Qed.

Notation "x '=P' y" := (set1P x y) (at level 70, no associativity).

Definition eqP := set1P.
Implicit Arguments eqP [d x y].
Prenex Implicits eqP.

Lemma eq_refl : forall (d : eqType) (x : d), x == x.
Proof. by move=> *; apply/eqP. Qed.

Lemma eq_sym : forall (d : eqType) (x y : d), (x == y) = (y == x).
Proof. by move=> *; apply/eqP/eqP. Qed.

(* A short proof of the K axiom (proof-irrelevance for x = x) on eqTypes. *)

Theorem eq_axiomK : forall (d : eqType) (x : d) (Ex : x = x), Ex = erefl x.
Proof.
move=> d x Exx.
have Er: forall E, eq_ind x (fun y => y = x) E x E = erefl x.
  by case: {2 3 4 6 7 8}x /.
case (Er (if x =P x is Reflect_true E then E else Exx)).
case: {2 4 6 8 10 12 14 16}x / {-3}Exx; case: (x =P x) => [E|[]]; auto.
Qed.

Lemma eq_irrelevance : forall (d : eqType) (x y : d) (E E' : x = y), E = E'.
Proof. by move=> d x y; case: y / => E; rewrite [E]eq_axiomK. Qed.

(* Comparison for booleans. *)

Lemma eqbP : reflect_eq eqb.
Proof. by do 2 case; constructor. Qed.

Canonical Structure bool_eqType := EqType eqbP.

Lemma eqbE : eqb = set1. Proof. done. Qed.

Lemma bool_irrelevance : forall (x y : bool) (E E' : x = y), E = E'.
Proof. exact: eq_irrelevance. Qed.

(* Subsets and relations, defined by their characteristic functions.       *)

Section EqSet.

Variable d : eqType.

Definition set := d -> bool.
Definition rel := d -> set.

Definition sub_set (a a' : set) : Prop := forall x : d, a x -> a' x.
Definition sub_rel (e e' : rel) : Prop := forall x y : d, e x y -> e' x y.

Definition set2 (x1 x2 : d) : set := fun y => (x1 == y) || (x2 == y).
Definition set3 (x1 x2 x3 : d) : set :=
  fun y => or3b (x1 == y) (x2 == y) (x3 == y).
Definition set4 (x1 x2 x3 x4 : d) : set :=
  fun y => or4b (x1 == y) (x2 == y) (x3 == y) (x4 == y).
Definition setU (a b : set) : set := fun x => a x || b x.
Definition setU1 (x : d) (a : set) : set := fun y => (x == y) || a y.
Definition setI (a b : set) : set := fun x => a x && b x.
Definition setC (a : set) : set := fun x => ~~ a x.
Definition setC1 (x : d) : set := fun y => x != y.
Definition setD (a b : set) : set := fun x => ~~ b x && a x.
Definition setD1 (a : set) (x : d) : set := fun y => (x != y) && a y.

Definition set1f (f : d -> d) : rel := fun x => set1 (f x).
Definition relU (e e' : rel) : rel := fun x => setU (e x) (e' x).

Lemma set11 : forall x : d, set1 x x. Proof. exact: eq_refl. Qed.

Lemma setU11 : forall x a, setU1 x a x.
Proof. by move=> *; rewrite /setU1 set11. Qed.

Lemma setU1r : forall x a, sub_set a (setU1 x a).
Proof. by move=> x a y Hy; rewrite /setU1 Hy orbT. Qed.

Lemma setU1P : forall x (a : set) y, reflect (x = y \/ a y) (setU1 x a y).
Proof.
by move=> x a y; apply: (iffP orP); case; auto; left; [ apply: eqP | apply/eqP ].
Qed.

Lemma setC11 : forall x, setC1 x x = false.
Proof. by move=> *; rewrite /setC1 set11. Qed.

Lemma setD11 : forall x a, setD1 a x x = false.
Proof. by move=> *; rewrite /setD1 set11. Qed.

Lemma set21 : forall x1 x2, set2 x1 x2 x1.
Proof. by move=> *; rewrite /set2 set11. Qed.

Lemma set22 : forall x1 x2, set2 x1 x2 x2.
Proof. by move=> *; rewrite /set2 set11 orbT. Qed.

Lemma set31 : forall x1 x2 x3, set3 x1 x2 x3 x1.
Proof. by move=> *; rewrite /set3 set11. Qed.

Lemma set32 : forall x1 x2 x3, set3 x1 x2 x3 x2.
Proof. by move=> *; rewrite /set3 set11 !orbT . Qed.

Lemma set33 : forall x1 x2 x3, set3 x1 x2 x3 x3.
Proof. by move=> *; rewrite /set3 set11 !orbT. Qed.

Lemma sub_relUl : forall e e', sub_rel e (relU e e').
Proof. by move=> e e' x y Hxy; rewrite /relU /setU Hxy. Qed.

Lemma sub_relUr : forall e e', sub_rel e' (relU e e').
Proof. by move=> e e' x y Hxy; rewrite /relU /setU Hxy orbT. Qed.

End EqSet.

Hint Resolve set11.

Prenex Implicits set1f set2 set3 set4 setU setD setD1 setI setC setC1.

Notation set0 := (fun _ : EqType.sort _ => false).

Coercion setA (d : eqType) : set d := fun x : d => true.

Identity Coercion membership : set >-> Funclass.

Implicit Arguments setU1P [d x a y].
Prenex Implicits setU1 setU1P.

(* Lemmas for reflected equality and endo functions.   *)

Section EqFun.

Lemma inj_eq : forall (d d' : eqType) (h : d -> d'),
  injective h -> forall x y, (h x == h y) = (x == y).
Proof. by move=> d d' h *; apply/eqP/eqP => *; [ auto | congr h ]. Qed.

Variables (d : eqType) (f g : d -> d).

Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof. move/can_inj; exact: inj_eq. Qed.

Lemma bij_eq : bijective f -> forall x y, (f x == f y) = (x == y).
Proof. move/bij_inj; apply: inj_eq. Qed.

Lemma can2_eq : cancel f g -> cancel g f -> forall x y, (f x == y) = (x == g y).
Proof. by move=> Ef Eg x y; rewrite -{1}[y]Eg; exact: can_eq. Qed.

Lemma inv_eq : involutive f -> forall x y, (f x == y) = (x == f y).
Proof. by move=> Ef x y; rewrite -(inj_eq (inv_inj Ef)) Ef. Qed.

Variable d' : eqType.

Definition preimage k (a : set d') : set d := fun x => a (k x).

(* The invariant of an function f wrt a projection k is the set of points that *)
(* have the same projection as their image. We use this mainly with k a        *)
(* coloring function (in fact "coloring" a map is defined using "invariant").  *)

Definition invariant (k : d -> d') : set d := fun x => (k (f x) == k x).

Lemma invariant_comp : forall h k, sub_set (invariant k) (invariant (h \o k)).
Proof. by move=> h k x Dkfx; rewrite /comp /invariant (eqP Dkfx) set11. Qed.

Lemma invariant_inj : forall h k, injective h -> invariant (h \o k) =1 invariant k.
Proof. move=> h k Hh x; exact: (inj_eq Hh). Qed.

End EqFun.

Prenex Implicits preimage.

(* Various  constructions (however, we tend to roll out our own, in *)
(* order to retain control over the equality predicate).                   *)

Section ComparableType.

Variable d : Type.

Definition comparable := forall x y : d, {x = y} + {x <> y}.

Hypothesis Hcompare : forall x y : d, {x = y} + {x <> y}.

Definition compareb x y := if Hcompare x y is left _ then true else false.

Lemma compareP : reflect_eq compareb.
Proof. by move=> x y; rewrite /compareb; case (Hcompare x y); constructor. Qed.

Definition comparableType := EqType compareP.

End ComparableType.

Definition eq_comparable (d : eqType) : comparable d :=
  fun x y => decP (x =P y).

Section SubEqType.

Variables (d : eqType) (a : set d).

Record eq_sig : Type := EqSig {val : d; valP : a val}.

Lemma val_eqP : reflect_eq (fun u v => val u == val v).
Proof.
move=> [x Hx] [y Hy]; apply: (iffP eqP) => Hxy; last by congr val.
by simpl in Hxy; rewrite -Hxy in Hy |- *; rewrite (bool_irrelevance Hy Hx).
Qed.

Canonical Structure sub_eqType := EqType val_eqP.

Lemma val_eqE : forall u v : sub_eqType, (val u == val v) = (u == v).
Proof. done. Qed.

Lemma val_inj : injective val.
Proof. by move=> u v; move/eqP; move/val_eqP. Qed.

Definition insub x :=
  if @idP (a x) is Reflect_true Hx then Some (EqSig Hx) else None.

CoInductive insub_spec (x : d) : option sub_eqType -> Type :=
  | Some_val u : a x -> val u = x -> insub_spec x (Some u)
  | None_val : ~~ a x -> insub_spec x None.

Lemma insubP : forall x, insub_spec x (insub x).
Proof.
move=> x; rewrite /insub; case: {2}(a x) / (@idP (a x)); first by left.
by move/negP; right.
Qed.

End SubEqType.

Implicit Arguments EqSig [d].
Implicit Arguments val_eqP [d a x y].
Prenex Implicits val val_eqP.

Section ProdEqType.

Variable d1 d2 : eqType.

Record eq_pair : Type := EqPair {eq_pi1 : d1; eq_pi2 : d2}.

Definition pair_eq u v :=
  let: EqPair x1 x2 := u in let: EqPair y1 y2 := v in (x1 == y1) && (x2 == y2).

Lemma pair_eqP : reflect_eq pair_eq.
Proof.
move=> [x1 x2] [y1 y2] /=; apply: (iffP idP) => [|[<- <-]]; last by rewrite !set11.
by case/andP; do 2 move/eqP->.
Qed.

Canonical Structure prod_eqType := EqType pair_eqP.

Lemma pair_eqE : pair_eq = set1. Proof. done. Qed.

Lemma pair_eq1 : forall u v : prod_eqType, u == v -> eq_pi1 u == eq_pi1 v.
Proof. by move=> [x1 x2] [y1 y2]; case/andP. Qed.

Lemma pair_eq2 : forall u v : prod_eqType, u == v -> eq_pi2 u == eq_pi2 v.
Proof. by move=> [x1 x2] [y1 y2]; case/andP. Qed.

Definition eq_prod a1 a2 : set prod_eqType := 
  fun u => a1 (eq_pi1 u) && a2 (eq_pi2 u).

End ProdEqType.

Implicit Arguments pair_eqP [d1 d2].
Prenex Implicits eq_pi1 eq_pi2 pair_eqP.

Section SumEqType.

Variables (index : eqType) (dom_at : index -> eqType).

Record eq_tagged : Type := EqTagged {tag : index; tagged : dom_at tag}.

Definition tagged_as (u v : eq_tagged) : dom_at (tag u) :=
  if tag u =P tag v is Reflect_true Huv then
    eq_rect_r dom_at (tagged v) Huv 
  else tagged u.

Lemma tagged_as_same : forall i (x y : dom_at i),
  tagged_as (EqTagged x) (EqTagged y) = y.
Proof.
move=> i x y; rewrite /tagged_as /=; case: (i =P i) => [Hii|[]]; auto.
by rewrite (eq_axiomK Hii).
Qed.

Definition tagged_eq u v :=
  (tag u == tag v) && (tagged u == tagged_as u v).

Lemma tagged_eqP : reflect_eq tagged_eq.
Proof.
move=> [i x] [j y]; rewrite /tagged_eq /=.
case: (i =P j) y => [<-|Hij] y; last by right; case.
by apply: (iffP eqP) => [->|<-]; rewrite tagged_as_same.
Qed.

Canonical Structure sum_eqType := EqType tagged_eqP.

Lemma tagged_eqE : tagged_eq = set1. Proof. done. Qed.

Lemma sum_eq_tag : forall u v : eq_tagged, u == v -> tag u == tag v.
Proof.
by move=> [i x] [j y]; rewrite -{1}tagged_eqE /tagged_eq /=; case (i == j).
Qed.

Lemma sum_eq_tagged : forall i (x y : dom_at i),
  (EqTagged x == EqTagged y) = (x == y).
Proof. by move=> *; rewrite -{1}tagged_eqE /tagged_eq /= set11 tagged_as_same. Qed.

Definition eq_family := forall i : index, set (dom_at i).

Definition eq_sum (a : eq_family) : set sum_eqType := fun u => a (tag u) (tagged u).

End SumEqType.

Implicit Arguments tagged [index dom_at].
Implicit Arguments tagged_eqP [index dom_at x y].

Prenex Implicits tag tagged tagged_eqP.

Unset Implicit Arguments.