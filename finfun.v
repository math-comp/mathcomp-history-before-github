Require Import ssreflect.
Require Import seq.
Require Import eqtype.
Require Import ssrnat.
Require Import ssrfun.
Require Import ssrbool.
Require Import fintype.
Require Import tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Def.

Variables (aT : finType) (rT : Type).

Inductive finfun : Type := Finfun of tuple #|aT| rT.

Definition finfun_for of phant (aT -> rT) : predArgType := finfun.

Notation fT := (finfun_for (Phant (aT -> rT))).

Definition fgraph f := let: Finfun t := f in t.

CoInductive app_ffun_spec (f : finfun) (x : aT) : rT -> Prop :=
  AppFfunSpec : app_ffun_spec f x (tsub (fgraph f) (enum_rank x)).

Lemma ffun_fun_def : forall ff, {f | forall x, app_ffun_spec ff x (f x)}.
Proof. by move=> f; exists (fun x => tsub (fgraph f) (enum_rank x)). Qed.

Definition fun_of_ffun f := sval (ffun_fun_def f).

Coercion fun_of_ffun : finfun >-> Funclass.

Canonical Structure finfun_subType := NewType fgraph finfun_rect vrefl.
Canonical Structure finfun_for_subType := Eval hnf in [subType of fT].

Lemma app_ffunP : forall (f : fT) x, app_ffun_spec f x (f x).
Proof. move=> f; exact: (svalP (ffun_fun_def f)). Qed.

Lemma fgraph_maps : forall f : fT, fgraph f = [tuple of maps f (enum aT)].
Proof.
move=> f; apply: eq_from_tsub => i; rewrite tsub_maps; case: app_ffunP.
by congr tsub; rewrite -[tsub _ _]enum_val_sub enum_valK.
Qed.

Lemma maps_ffun_enum : forall f : fT, maps f (enum aT) = val f.
Proof. by move=> f; rewrite /= fgraph_maps. Qed.

Lemma make_ffun : forall f, {ff : fT | ff =1 f}.
Proof.
move=> f; exists (Finfun [tuple of maps f (enum aT)]) => x.
by case: app_ffunP; rewrite tsub_maps -[tsub _ _]enum_val_sub enum_rankK.
Qed.

Definition ffun_of f : fT := sval (make_ffun f).

Lemma ffunE : forall f, ffun_of f =1 f.
Proof. by rewrite /ffun_of => f; case: make_ffun. Qed.

Lemma ffunP : forall f1 f2 : fT, f1 =1 f2 <-> f1 = f2.
Proof.
move=> f1 f2; split=> [eq_f12 | -> //]; do 2!apply: val_inj => /=.

by rewrite -!maps_ffun_enum (eq_maps eq_f12).
Qed.

Lemma ffunK : cancel fun_of_ffun ffun_of.
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

End Def.

Notation "{ 'ffun' fT }" := (finfun_for (Phant fT))
  (at level 0, format "{ 'ffun'  '[hv' fT ']' }") : type_scope.

Notation "'F_' ( n )" := {ffun I_(n) -> I_(n)}
  (at level 0, format "'F_' ( n )") : type_scope.

Notation "[ 'ffun' x : aT => F ]" := (ffun_of (fun x : aT => F))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'ffun' : aT => F ]" := (ffun_of (fun _ : aT => F))
  (at level 0, only parsing) : fun_scope.

Notation "[ 'ffun' x => F ]" := [ffun x : _ => F]
  (at level 0, x ident, format "[ 'ffun'  x  =>  F ]") : fun_scope.

Notation "[ 'ffun' => F ]" := [ffun : _ => F]
  (at level 0, format "[ 'ffun' =>  F ]") : fun_scope.

Section EqFinfun.

Variables (aT : finType) (rT : eqType).

Notation fT := {ffun aT -> rT}.

Canonical Structure finfun_eqType := Eval hnf in [subEqType for @fgraph aT rT].
Canonical Structure finfun_for_eqType := Eval hnf in [eqType of fT].

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

End EqFinfun.

Section FinFunSpace.

Variables aT rT : finType.

Notation fT := {ffun aT -> rT}.

Canonical Structure finfun_finType :=
  Eval hnf in [subFinType of finfun_eqType aT rT].
Canonical Structure finfun_for_finType :=
  Eval hnf in [finType of finfun_for_eqType aT rT].

Lemma card_pfamily : forall y0 d (F : aT -> pred rT),
  #|pfamily y0 d F| = foldr (fun x m => #|F x| * m) 1 (enum d).
Proof.
move=> y0 d F; have:= (uniq_enum d); have:= (mem_enum d). 
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
  rewrite ffunE -[d _]eq_ds in_adds /=.
  by case: (x =P x0) => //= -> _; rewrite nsx0 /=.
exists (g2 (y, f)); last first.
  congr (_, _); first by rewrite ffunE eqxx.
  apply/ffunP=> x; rewrite !ffunE /=; case: (x =P x0) => // ->{x}.
  by have:= forallP Ff x0; rewrite /= nsx0; move/eqP.
apply/forallP=> x; have:= forallP Ff x; rewrite -[d _]eq_ds ffunE in_adds.
by case: (x =P x0) => //= ->.
Qed.

Lemma card_family : forall F : aT -> pred rT,
  #|family F| = foldr (fun x m => #|F x| * m) 1 (enum aT).
Proof.
move=> F; case: (pickP rT) => [y0 _ | rT0].
  by rewrite -(card_pfamily y0); apply: eq_card.
case: enum (mem_enum aT) => [aT0 | x0 e _]; last first.
  by rewrite /= !eq_card0 // => [f | y]; [have := rT0 (f x0) | have:= rT0 y].
have naT: forall x : aT, _ by move=> P x; have:= aT0 x.
rewrite /= -(card1 [ffun x => naT rT x]); apply: eq_card => f'.
apply/forallP/eqP=> _; first 1 [apply/ffunP] => x; exact: naT.
Qed.

Lemma card_pffun_on : forall y0 d r, #|pffun_on y0 d r| = #|r| ^ #|d|.
Proof.
by move=> y0 d r; rewrite card_pfamily (cardE d); elim: enum => //= _ {d}d ->.
Qed.

Lemma card_ffun_on : forall r, #|ffun_on r| = #|r| ^ #|aT|.
Proof.
by move=> r; rewrite card_family (cardE aT); elim: enum => //= _ e ->.
Qed.

Lemma card_ffun : #|fT| = #|rT| ^ #|aT|.
Proof.
rewrite -card_ffun_on; apply: eq_card => f; symmetry; exact/forallP.
Qed.

End FinFunSpace.

Section FinPowerSet.

Variable eT : finType.
Variable A : pred eT.

Definition powerset := pffun_on false A predT.

Lemma card_powerset : #|powerset| = 2 ^ #|A|.
Proof. rewrite -card_bool; exact: card_pffun_on. Qed.

End FinPowerSet.

Lemma card_tuple : forall n (T : finType), #|tuple n T| = #|T| ^ n.
Proof. by move=> n T; rewrite -[n]card_ord -card_ffun card_sub. Qed.

