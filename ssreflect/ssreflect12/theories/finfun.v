(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.

(*******************************************************************************)
(* This files contains the definitions of:                                     *)
(*   finfun_type : type of functions with finite domain. the function is       *)
(*                 represented by its graph.                                   *)
(*   fun_of_fin : Coercion from finfun_type to FunClass.                       *)
(*   finfun : construct an element of finfun_type from a function that have a  *)
(*            finite domain. This is the RECOMMENDED interface to build an     *) 
(*            element of finfun_type.                                          *)
(*   family : definition of family of set as a set of finite domain function.  *)
(* In addition to the lemmas relevant to these definitions, this file also     *)
(* contains generic lemmas when the codomain of the finite function is an      *) 
(* eqType or a finType. Canonical Structure are also defined in this two cases *)
(*******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Def.

Variables (aT : finType) (rT : Type).

Inductive finfun_type : predArgType := Finfun of #|aT|.-tuple rT.

Definition finfun_of of phant (aT -> rT) := finfun_type.

Identity Coercion type_of_finfun : finfun_of >-> finfun_type.

Definition fgraph f := let: Finfun t := f in t.

Canonical Structure finfun_subType :=
  Eval hnf in [newType for fgraph by finfun_type_rect].

End Def.

Notation "{ 'ffun' fT }" := (finfun_of (Phant fT))
  (at level 0, format "{ 'ffun'  '[hv' fT ']' }") : type_scope.

Notation Local fun_of_fin_def :=
  (fun aT rT f x => tnth (@fgraph aT rT f) (enum_rank x)).

Notation Local finfun_def :=
  (fun aT rT f => @Finfun aT rT [tuple of map f (enum aT)]).

Module Type FunFinfunSig.
Parameter fun_of_fin : forall aT rT, finfun_type aT rT -> aT -> rT.
Coercion fun_of_fin : finfun_type >-> Funclass.
Parameter finfun : forall (aT : finType) rT, (aT -> rT) -> {ffun aT -> rT}.
Axiom fun_of_finE : fun_of_fin = fun_of_fin_def.
Axiom finfunE : finfun = finfun_def.
End FunFinfunSig.

Module FunFinfun : FunFinfunSig.
Definition fun_of_fin := fun_of_fin_def.
Definition finfun := finfun_def.
Lemma fun_of_finE : fun_of_fin = fun_of_fin_def. Proof. by []. Qed.
Lemma finfunE : finfun = finfun_def. Proof. by []. Qed.
End FunFinfun.

Notation fun_of_fin := FunFinfun.fun_of_fin.
Notation finfun := FunFinfun.finfun.
Canonical Structure fun_of_fin_unlock := Unlockable FunFinfun.fun_of_finE.
Canonical Structure finfun_unlock := Unlockable FunFinfun.finfunE.

Notation "[ 'ffun' x : aT => F ]" := (finfun (fun x : aT => F))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'ffun' : aT => F ]" := (finfun (fun _ : aT => F))
  (at level 0, only parsing) : fun_scope.

Notation "[ 'ffun' x => F ]" := [ffun x : _ => F]
  (at level 0, x ident, format "[ 'ffun'  x  =>  F ]") : fun_scope.

Notation "[ 'ffun' => F ]" := [ffun : _ => F]
  (at level 0, format "[ 'ffun' =>  F ]") : fun_scope.

(* Lemma on the correspondance between finfun_type and finite domain function *)
Section PlainTheory.

Variables (aT : finType) (rT : Type).
Notation fT := {ffun aT -> rT}.

Canonical Structure finfun_of_subType := [subType of fT].

Lemma tnth_fgraph : forall (f : fT) i, tnth (fgraph f) i = f (enum_val i).
Proof. by move=> f i; rewrite [@fun_of_fin _]unlock enum_valK. Qed.

Lemma ffunE : forall f : aT -> rT, finfun f =1 f.
Proof.
move=> f x; rewrite [@finfun _]unlock unlock tnth_map.
by rewrite -[tnth _ _]enum_val_nth enum_rankK.
Qed.

Lemma fgraph_map : forall f : fT, fgraph f = [tuple of map f (enum aT)].
Proof.
move=> f; apply: eq_from_tnth => i; rewrite [@fun_of_fin _]unlock tnth_map.
by congr tnth; rewrite -[tnth _ _]enum_val_nth enum_valK.
Qed.

Lemma map_ffun_enum : forall f : fT, map f (enum aT) = val f.
Proof. by move=> f; rewrite /= fgraph_map. Qed.

Lemma ffunP : forall f1 f2 : fT, f1 =1 f2 <-> f1 = f2.
Proof.
move=> f1 f2; split=> [eq_f12 | -> //]; do 2!apply: val_inj => /=.
by rewrite -!map_ffun_enum (eq_map eq_f12).
Qed.

Lemma ffunK : cancel (@fun_of_fin aT rT) (@finfun aT rT).
Proof. move=> f; apply/ffunP; exact: ffunE. Qed.

Section Family.

Variable F : aT -> pred rT.

Definition family : pred fT := fun f => forallb x, F x (f x).

Lemma familyP : forall f : fT, reflect (forall x, F x (f x)) (family f).
Proof. move=> f; exact: forallP. Qed.

End Family.

Definition ffun_on r := family (fun _ => r).

Lemma ffun_onP : forall (r : pred rT) (f : fT),
  reflect (forall x, r (f x)) (ffun_on r f).
Proof. move=> r f; exact: forallP. Qed.

End PlainTheory.

(*******************************************************************************)

Lemma nth_fgraph_ord : forall T n (x0 : T) (i : 'I_n) f,
  nth x0 (fgraph f) i = f i.
Proof.
move=> T n x0 i f.
by rewrite -{2}(enum_rankK i) -tnth_fgraph (tnth_nth x0) enum_rank_ord.
Qed.

Section EqTheory.

Variables (aT : finType) (rT : eqType).

Notation fT := {ffun aT -> rT}.

Definition finfun_eqMixin :=
  Eval hnf in [eqMixin of finfun_type aT rT by <:].
Canonical Structure finfun_eqType := Eval hnf in EqType finfun_eqMixin.
Canonical Structure finfun_of_eqType := Eval hnf in [eqType of fT].

Section Partial.

Variables (y0 : rT) (d : pred aT).

Definition support T f : pred T := fun x => f x != y0.

Definition pfamily F :=
  family (fun i => if d i then F i else pred1 y0 : pred _).

Lemma pfamilyP : forall (F : aT -> pred rT) (f : fT),
  reflect (subpred (support f) d /\ forall x, d x -> F x (f x)) (pfamily F f).
Proof.
move=> F f; apply: (iffP forallP) => [f_pfam | [f_supp f_fam] x].
  split=> [x | x dx]; move/(_ x): f_pfam; last by rewrite dx.
  by rewrite /support /=; case: (d x) => //= ->.
case dx: (d x); [exact: f_fam | by apply/idPn; move/f_supp; rewrite dx].  
Qed.

Definition pffun_on r := pfamily (fun _ => r).

Lemma pffun_onP : forall r (f : fT),
  reflect (subpred (support f) d /\ subpred (image f d) r) (pffun_on r f).
Proof.
move=> r f; apply: (iffP (pfamilyP _ _)); case=> f_supp f_fam.
  split=> // y; case/imageP=> x dx ->{y}; exact: f_fam.
by split=> // x dx; apply: f_fam; apply/imageP; exists x.
Qed.

End Partial.

End EqTheory.

Definition finfun_choiceMixin aT (rT : choiceType) :=
  [choiceMixin of finfun_type aT rT by <:].
Canonical Structure finfun_choiceType aT rT :=
  Eval hnf in ChoiceType (finfun_choiceMixin aT rT).
Canonical Structure finfun_of_choiceType (aT : finType) (rT : choiceType) :=
  Eval hnf in [choiceType of {ffun aT -> rT}].

Definition finfun_countMixin aT (rT : countType) :=
  [countMixin of finfun_type aT rT by <:].
Canonical Structure finfun_countType aT (rT : countType) :=
  Eval hnf in CountType (finfun_countMixin aT rT).
Canonical Structure finfun_of_countType (aT : finType) (rT : countType) :=
  Eval hnf in [countType of {ffun aT -> rT}].
Canonical Structure finfun_subCountType aT (rT : countType) :=
  Eval hnf in [subCountType of finfun_type aT rT].
Canonical Structure finfun_of_subCountType (aT : finType) (rT : countType) :=
  Eval hnf in [subCountType of {ffun aT -> rT}].

(*******************************************************************************)

Section FinTheory.

Variables aT rT : finType.

Notation fT := {ffun aT -> rT}.
Notation ffT := (finfun_type aT rT).

Definition finfun_finMixin := [finMixin of ffT by <:].
Canonical Structure finfun_finType := Eval hnf in FinType finfun_finMixin.
Canonical Structure finfun_subFinType := Eval hnf in [subFinType of ffT].
Canonical Structure finfun_of_finType := Eval hnf in [finType of fT].
Canonical Structure finfun_of_subFinType := Eval hnf in [subFinType of fT].

Lemma card_pfamily : forall y0 d (F : aT -> pred rT),
  #|pfamily y0 d F| = foldr (fun x m => #|F x| * m) 1 (enum d).
Proof.
move=> y0 d F; have:= enum_uniq d; have:= mem_enum d. 
elim: {d}enum {2 4}d => [|x0 s IHs] d eq_ds => [_|] /=.
  rewrite -(card1 [ffun=> y0]); apply: eq_card => f.
  apply/familyP/eqP => [f_y0 | ->{f} x]; last by rewrite ffunE -[d _]eq_ds /=.
  by apply/ffunP=> x; move/(_ x): f_y0; rewrite -[d _]eq_ds ffunE; move/eqP.
case/andP; move/negPf=> nsx0; move/(IHs (mem s))=> <- {IHs}//.
pose g1 (f : fT) := (f x0, [ffun x => if x == x0 then y0 else f x]).
pose g2 (xf : rT * fT) := [ffun x => if x == x0 then xf.1 else xf.2 x].
have g1K : cancel g1 g2.
  move=> f; apply/ffunP=> x; rewrite ffunE /= !ffunE.
  by case: (x =P x0) => // ->.
rewrite -cardX -(card_image (can_inj g1K)).
apply: eq_card => [] [y f] /=.
apply/imageP/andP=> [[f' F_f'] [-> ->]| [Fy Ff]].
  split; first by have:= forallP F_f' x0; rewrite -[d _]eq_ds mem_head.
  apply/forallP=> x; have:= forallP F_f' x.
  rewrite ffunE -[d _]eq_ds in_cons /=.
  by case: (x =P x0) => //= -> _; rewrite nsx0 /=.
exists (g2 (y, f)); last first.
  congr (_, _); first by rewrite ffunE eqxx.
  apply/ffunP=> x; rewrite !ffunE /=; case: (x =P x0) => // ->{x}.
  by have:= forallP Ff x0; rewrite /= nsx0; move/eqP.
apply/forallP=> x; have:= forallP Ff x; rewrite -[d _]eq_ds ffunE in_cons.
by case: (x =P x0) => //= ->.
Qed.

Lemma card_family : forall F : aT -> pred rT,
  #|family F| = foldr (fun x m => #|F x| * m) 1 (enum aT).
Proof.
move=> F; case: (pickP rT) => [y0 _ | rT0].
  by rewrite -(card_pfamily y0); apply: eq_card.
case: enum (mem_enum aT) => [aT0 | x0 e _]; last first.
  by rewrite /= !eq_card0 // => [f | y]; [have := rT0 (f x0) | have := rT0 y].
have naT: forall x : aT, _ by move=> P x; have:= aT0 x.
rewrite /= -(card1 [ffun x => naT rT x]); apply: eq_card => f'.
apply/forallP/eqP=> _; first 1 [apply/ffunP] => x; exact: naT.
Qed.

Lemma card_pffun_on : forall y0 d r, #|pffun_on y0 d r| = #|r| ^ #|d|.
Proof.
move=> y0 d r; rewrite (cardE d) -(@eq_enum _ d) // card_pfamily.
by elim: (enum _) => //= _ ? ->; rewrite expnS.
Qed.

Lemma card_ffun_on : forall r, #|ffun_on r| = #|r| ^ #|aT|.
Proof.
move=> r; rewrite card_family cardT.
by elim: enum => //= _ e ->; rewrite expnS.
Qed.

Lemma card_ffun : #|fT| = #|rT| ^ #|aT|.
Proof.
rewrite -card_ffun_on; apply: eq_card => f; symmetry; exact/forallP.
Qed.

End FinTheory.

(*******************************************************************************)

Section FinPowerSet.

Variable eT : finType.
Variable A : pred eT.

Definition powerset := pffun_on false A predT.

Lemma card_powerset : #|powerset| = 2 ^ #|A|.
Proof. rewrite -card_bool; exact: card_pffun_on. Qed.

End FinPowerSet.

(*******************************************************************************)