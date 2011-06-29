(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
Require Import bigop ssralg finset fingroup zmodp.
Require Import poly.

(*****************************************************************************)
(*     x <= y == x is smaller than y                                         *)
(*      x < y := (x <= y) && (x != y)                                        *)
(* cpable x y == x and y are comparable, i.e. x <= y or y <= x               *)
(*      sgr x == sign of x, equals (0 : R) if and only x == 0,               *)
(*            equals (1 : R) if x is positive, and -1 otherwise              *)
(*     absr x == x if x is positive -x otherwise                             *)
(*   minr x y == minimum of x y                                              *)
(*   maxr x y == maximum of x y                                              *)
(*                                                                           *)
(* - monotonity for functions w.r.t. a relation,                             *)
(* {wmono f :/ a >-> r } == f is a montone with respect to relations         *)
(*                                a and r                                    *)
(* {wmono f : x y / a >-> r } == f is a montone with respect to              *)
(*                         relations (fun x => a) and (fun x => r)           *)
(* {wmono f :/ a } == f is monotone with respect to relation a               *)
(* {wmono f : x y / a } == f is monotone with respect to (fun x y => a)      *)
(* {wmono f :/~ a } == f is non monotone with respect to relation a          *)
(* {wmono f : x y /~ a } == f is non monotone with respect to (fun x y => a) *)
(* {mono f : x y / a >-> r } et al. := r (f x) (f y) = a x y                 *)
(*                                                                           *)
(* - list of prefixies :                                                     *)
(*   p : positive                                                            *)
(*   n : negative                                                            *)
(*   sp : strictly positive                                                  *)
(*   sn : strictly negative                                                  *)
(*   i : interior = in [0, 1] of ]0, 1[                                      *)
(*   e : exterior = in [1, +oo[ or ]1; +oo[                                  *)
(*   w : non strict (weak) monotony                                          *)
(*****************************************************************************)


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory.

Reserved Notation  "`| x |" (at level 0, x at level 99, format "`| x |").
Reserved Notation "x <= y :> T" (at level 70, y at next level).
Reserved Notation "x >= y :> T" (at level 70, y at next level, only parsing).
Reserved Notation "x < y :> T" (at level 70, y at next level).
Reserved Notation "x > y :> T" (at level 70, y at next level, only parsing).
(* Reserved Notation "x ?= y" (at level 70). *)
(* Reserved Notation "x ?= y :> T"
   (at level 70, y at next level, only parsing). *)

Section extra_ssrnat.

Lemma wlog_leq P : (forall a b, P b a -> P a b)
  -> (forall a b, P a (a + b)%N) -> forall a b, P a b.
Proof.
move=> sP hP a b; wlog: a b / a <= b; last by move/subnKC<-; apply: hP.
by move=> hwlog; case: (leqP a b)=>[|/ltnW] /hwlog // /sP.
Qed.

Lemma wlog_ltn P : (forall a, P a a) -> (forall a b, (P b a -> P a b))
  -> (forall a b, P a (a + b.+1)%N) -> forall a b, P a b.
Proof. by move=> rP sP hP; apply: wlog_leq=> // a [|n //]; rewrite addn0. Qed.

End extra_ssrnat.


Section extra_ssralg.

Lemma invr_eq1 (F : unitRingType) (x : F): (x^-1 == 1 :> F) = (x == 1).
Proof. by rewrite (can2_eq (@invrK _) (@invrK _)) invr1. Qed.

Lemma prodf_seq_eq0 (R : idomainType) (I : eqType)
  (s : seq I) (P : pred I) (F : I -> R) :
   (\prod_(i <- s | P i) F i == 0) = (has (fun i => P i && (F i == 0)) s).
Proof. by rewrite (big_morph _ (@mulf_eq0 _) (oner_eq0 _)) big_has_cond. Qed.

Lemma prodf_seq_neq0 (R : idomainType) (I : eqType)
  (s : seq I) (P : pred I) (F : I -> R) :
   (\prod_(i <- s | P i) F i != 0) = (all (fun i => P i ==> (F i != 0)) s).
Proof.
rewrite prodf_seq_eq0 -all_predC; apply: eq_all => i /=.
by rewrite implybE negb_and.
Qed.

End extra_ssralg.

Section extra_ssrfun.

Variables (aT rT sT : Type) (f : aT -> rT).

Definition monotone (aR rR : _ -> _ -> Prop) : Prop := forall x y, aR x y -> rR (f x) (f y).
Definition stricty_monotone (aR rR : rel _) := forall x y, rR (f x) (f y) = aR x y.

End extra_ssrfun.

(* weak *)
Notation "{ 'wmono' f :/ a >-> r }" :=
  (monotone f a r)
  (at level 0, f at level 99, format "{ 'wmono'  f  :/  a  >->  r }") : type_scope.

Notation "{ 'wmono' f :/~ a >-> r }" :=
  (monotone f a (fun x y => r y x))
  (at level 0, f at level 99, format "{ 'wmono'  f  :/~  a  >->  r }") : type_scope.

Notation "{ 'wmono' f :/ a }" :=
  (monotone f a a)
  (at level 0, f at level 99, format "{ 'wmono'  f  :/  a }") : type_scope.

Notation "{ 'wmono' f :/~ a }" :=
  (monotone f a (fun y x => a x y))
  (at level 0, f at level 99, format "{ 'wmono'  f  :/~  a }") : type_scope.

Notation "{ 'wmono' f : x y / a >-> r }" :=
  (monotone f (fun x y => a) (fun x y => r))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'wmono'  f  :  x  y  /  a  >->  r }") : type_scope.

Notation "{ 'wmono' f : x y / a }" :=
  (monotone f (fun x y => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'wmono'  f  :  x  y  /  a }") : type_scope.

Notation "{ 'wmono' f : x y /~ a }" :=
  (monotone f (fun x y => a) (fun y x => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'wmono'  f  :  x  y  /~  a }") : type_scope.

(* strict *)
Notation "{ 'mono' f :/ a >-> r }" :=
  (stricty_monotone f a r)
  (at level 0, f at level 99, format "{ 'mono'  f  :/  a  >->  r }") : type_scope.

Notation "{ 'mono' f :/~ a >-> r }" :=
  (stricty_monotone f (fun x y => a y x) r)
  (at level 0, f at level 99, format "{ 'mono'  f  :/~  a  >->  r }") : type_scope.

Notation "{ 'mono' f :/ a }" :=
  (stricty_monotone f a a)
  (at level 0, f at level 99, format "{ 'mono'  f  :/  a }") : type_scope.

Notation "{ 'mono' f :/~ a }" :=
  (stricty_monotone f (fun y x => a x y) a)
  (at level 0, f at level 99, format "{ 'mono'  f  :/~  a }") : type_scope.

Notation "{ 'mono' f : x y / a >-> r }" :=
  (stricty_monotone f (fun x y => a) (fun x y => r))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'mono'  f  :  x  y  /  a  >->  r }") : type_scope.

Notation "{ 'mono' f : x y / a }" :=
  (stricty_monotone f (fun x y => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'mono'  f  :  x  y  /  a }") : type_scope.

Notation "{ 'mono' f : x y /~ a }" :=
  (stricty_monotone f (fun y x => a) (fun x y => a))
  (at level 0, f at level 99, x ident, y ident,
   format "{ 'mono'  f  :  x  y  /~  a }") : type_scope.

Section monotony.

Variables (aT rT sT : Type) (f : aT -> rT) (g : rT -> aT).
Variable (aR : rel aT) (rR : rel rT).

Lemma monoW : {mono f :/ aR >-> rR} -> {wmono f :/ aR >-> rR}.
Proof. by move=> hf x y axy; rewrite hf. Qed.

Hypothesis fgK : cancel g f.

Lemma monoRL : {wmono f :/ aR >-> rR} -> forall x y, aR (g x) y -> rR x (f y).
Proof. by move=> Hf x y /Hf; rewrite fgK. Qed.

Lemma monoLR : {wmono f :/ aR >-> rR} -> forall x y, aR x (g y) -> rR (f x) y.
Proof. by move=> Hf x y /Hf; rewrite fgK. Qed.

Lemma w2mono : {wmono f :/ aR >-> rR} -> {wmono g :/ rR >-> aR}
  -> {mono g :/ rR >-> aR}.
Proof.
move=> mf mg x y; case: (boolP (rR _ _))=> [/mg //|].
by apply: contraNF=> /mf; rewrite !fgK.
Qed.

Lemma mono2LR : {mono f :/ aR >-> rR} -> forall x y, rR (f x) y = aR x (g y).
Proof. by move=> mf x y; rewrite -{1}[y]fgK mf. Qed.

Lemma mono2RL : {mono f :/ aR >-> rR} -> forall x y, rR x (f y) = aR (g x) y.
Proof. by move=> mf x y; rewrite -{1}[x]fgK mf. Qed.

Lemma can_mono : {mono f :/ aR >-> rR} -> {mono g :/ rR >-> aR}.
Proof. by move=> mf x y /=; rewrite -mf !fgK. Qed.

End monotony.

Section monotony_in.

Variables (aT rT sT : predArgType) (f : aT -> rT) (g : rT -> aT).
Variable (aD : pred aT).
Variable (aR : rel aT) (rR : rel rT).

Notation rD := [pred x | g x \in aD].

Lemma monoW_in : {in aD &, {mono f :/ aR >-> rR}}
  -> {in aD &, {wmono f :/ aR >-> rR}}.
Proof. by move=> hf x y hx hy axy; rewrite hf. Qed.

Hypothesis fgK_on : {on aD, cancel g & f}.

Lemma monoRL_in : {in aD &, {wmono f :/ aR >-> rR}} ->
  forall x y, x \in rD -> y \in aD -> aR (g x) y -> rR x (f y).
Proof. by move=> Hf x y hx hy /Hf; rewrite fgK_on //; apply. Qed.

Lemma monoLR_in :  {in aD &, {wmono f :/ aR >-> rR}} ->
  forall x y, x \in aD -> g y \in aD -> aR x (g y) -> rR (f x) y.
Proof. by move=> Hf x y hx hy /Hf; rewrite fgK_on //; apply. Qed.

Lemma w2mono_in :  {in aD &, {wmono f :/ aR >-> rR}}
  -> {in rD &, {wmono g :/ rR >-> aR}} -> {in rD &, {mono g :/ rR >-> aR}}.
Proof.
move=> mf mg x y hx hy; case: (boolP (rR _ _))=> [/mg //|]; first exact.
by apply: contraNF=> /mf; rewrite !fgK_on //; apply.
Qed.

Lemma mono2LR_in : {in aD &, {mono f :/ aR >-> rR}}
  -> forall x y, x \in aD -> y \in rD -> rR (f x) y = aR x (g y).
Proof. by move=> mf x y hx hy; rewrite -{1}[y]fgK_on // mf. Qed.

Lemma mono2RL_in : {in aD &, {mono f :/ aR >-> rR}}
  -> forall x y, x \in rD -> y \in aD -> rR x (f y) = aR (g x) y.
Proof. by move=> mf x y hx hy; rewrite -{1}[x]fgK_on // mf. Qed.

Lemma can_mono_in : {in aD &, {mono f :/ aR >-> rR}}
  -> {in rD &, {mono g :/ rR >-> aR}}.
Proof. by move=> mf x y hx hy /=; rewrite -mf // !fgK_on. Qed.

End monotony_in.

Module OrderedRing.

Module PartialOrder.

Record mixin_of (R : ringType) := Mixin {
  le : rel R;
  _ : le 0 0;
  _ : le 0 1;
  _ : forall x y, le 0 x -> le 0 y -> le 0 (x + y);
  _ : forall x y, le 0 x -> le 0 y -> le 0 (x * y);
  _  : forall x, le 0 x -> le 0 (- x) -> x = 0;
  _  : forall x y, le x y = le 0 (y - x)
}.


Section PosMixin.
Variable R : GRing.IntegralDomain.type.
Variable pos : pred R.
Hypothesis pos0 : pos 0.
Hypothesis pos1 : pos 1.
Hypothesis pos_add : forall x y, pos x -> pos y -> pos (x + y).
Hypothesis pos_mul : forall x y, pos x -> pos y -> pos (x * y).
Hypothesis pos_eq0  : forall x,  pos x -> pos (-x) -> x = 0.

Definition le_pos x y := (pos (-x + y)).
Lemma le_pos00 : le_pos 0 0.
Proof. by rewrite /le_pos oppr0 add0r. Qed.
Lemma le_pos01 : le_pos 0 1.
Proof. by rewrite /le_pos oppr0 add0r. Qed.
Lemma le_pos0_add x y : le_pos 0 x -> le_pos 0 y -> le_pos 0 (x + y).
Proof. by rewrite /le_pos !oppr0 !add0r; apply: pos_add. Qed.
Lemma le_pos0_mul x y : le_pos 0 x -> le_pos 0 y -> le_pos 0 (x * y).
Proof. by rewrite /le_pos !oppr0 !add0r; apply: pos_mul. Qed.
Lemma le_pos0_eq0 x : le_pos 0 x -> le_pos 0 (-x) -> x = 0.
Proof. by rewrite /le_pos !oppr0 !add0r; apply: pos_eq0. Qed.
Lemma sub_pos_ge0 x y : le_pos x y = le_pos 0 (y - x).
Proof. by rewrite /le_pos !oppr0 !add0r addrC. Qed.

Definition PosMixin := Mixin le_pos00 le_pos01 le_pos0_add le_pos0_mul le_pos0_eq0 sub_pos_ge0.
End PosMixin.

Local Notation ring_mixin_of T b := (mixin_of (@GRing.Ring.Pack T b T)).

Section Generic.

(* The BF-prefixed bound variable names are a backward-compatibility patch
   between coq-8.2-1 and coq-trunk r12661 and later
*)

(* Implicits *)
Variables (BFtype base_type : Type) (BFclass_of base_of : Type -> Type).
Variable to_ring : forall T, base_of T -> GRing.Ring.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, BFclass_of T -> Type -> BFtype.
Variable Class : forall T b, ring_mixin_of T (to_ring b) -> BFclass_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T b0 (m0 : ring_mixin_of T b0) :=
  fun bT b & phant_id (base_class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

End Generic.

Implicit Arguments
   gen_pack [BFtype base_type BFclass_of base_of to_ring base_sort].

Module IntegralDomain.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : GRing.IntegralDomain.class_of R;
  mixin : mixin_of (GRing.Ring.Pack base R)
}.
Local Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Local Coercion mixin : class_of >-> mixin_of.
Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.IntegralDomain.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.IntegralDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Open Scope ring_scope.

Module OrderDef.

Definition ler (R : IntegralDomain.type) : rel R := le (IntegralDomain.class R).
Notation ">=%R" := (@ler _) : ring_scope.
Notation "x <= y" := (ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.
Notation "<=%R" := [rel x y | y <= x] : ring_scope.

Definition ltr (R : IntegralDomain.type) : rel R :=
  fun x y => (x != y) && (x <= y :> R).
Notation ">%R" := (@ltr _) : ring_scope.
Notation "x < y"  := (ltr x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.
Notation "<%R" := [rel x y | y < x] : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Definition cpable (R : IntegralDomain.type) : rel R :=
  fun x y => (x <= y) || (y <= x).

Definition sgr (R : IntegralDomain.type) (x : R) : R :=
  if x == 0 then 0 else if 0 <= x then 1 else -1.

(* Definition cpr (R : IntegralDomain.type) : R -> R -> comparison :=  *)
(*   fun x y => if x == y then Eq else if x <= y then Gt else Lt. *)
(* Notation "?=%R" := (@cpr _) : ring_scope. *)
(* Notation "x ?= y" := (cpr x y) : ring_scope. *)
(* Notation "x ?= y :> T" := ((x : T) ?= (y : T)) : ring_scope. *)

(* Definition cpr_to_R (R : idomainType) : comparison -> R :=  *)
(*   fun c => match c with Eq => 0 | Gt => 1 | Lt => -1 end. *)

Definition absr (R : IntegralDomain.type) (x : R) :=
  if 0 <= x then x else - x.
Notation "`| x |" := (@absr _ x) : ring_scope.

Definition minr (R : IntegralDomain.type) (x y : R) :=
  if x <= y then x else y.
Definition maxr (R : IntegralDomain.type) (x y : R) :=
  if y <= x then x else y.


End OrderDef.

Import OrderDef.

Module IntegralDomainTheory.

Section IntegralDomainTheory.

Variable R : IntegralDomain.type.
Implicit Types x y z t : R.

(* Lemmas from the signature *)
Fact ler00 : 0 <= 0 :> R.
Proof. by case R => T [? []]. Qed.

Lemma ler01 : 0 <= 1 :> R.
Proof. by case R => T [? []]. Qed.

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= (x + y).
Proof. by case: R x y => T [? []]. Qed.

Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= (x * y).
Proof. by case: R x y => T [? []]. Qed.

Fact ler0_eq0 x : 0 <= x -> 0 <= (-x) -> x = 0.
Proof. by case: R x => T [? []]. Qed.

Lemma subr_ge0  x y : (0 <= (y - x)) = (x <= y).
Proof. by case: R x y => T [? []]. Qed.

Hint Resolve ler00.
Hint Resolve ler01.

(* General properties of ler and ltr : relation between them including *)
(*                                     transitivity                    *)

Lemma ler_anti : antisymmetric (@ler R).
Proof.
move=> x y /andP [pxy pyx]; apply/eqP; rewrite -subr_eq0; apply/eqP.
by apply: ler0_eq0; rewrite ?oppr_sub subr_ge0.
Qed.

Lemma ler_trans : transitive (@ler R).
Proof.
move=> x y z; rewrite -subr_ge0=> pxy; rewrite -subr_ge0=> pyz.
by move: (addr_ge0 pxy pyz); rewrite addrC addrA addrNK subr_ge0.
Qed.

Lemma lerr x : x <= x. Proof. by rewrite -subr_ge0 subrr. Qed.
Hint Resolve lerr.

Lemma ltr_neqAle x y : (x < y) = (x != y) && (x <= y). Proof. done. Qed.

Lemma ler_eqVlt x y : (x <= y) = (x == y) || (x < y).
Proof.
by rewrite ltr_neqAle; case xy: (x == y)=> //=; rewrite (eqP xy) lerr.
Qed.

Lemma ltr01 : 0 < 1 :> R. Proof. by rewrite ltr_neqAle eq_sym oner_eq0. Qed.
Hint Resolve ltr01.

Definition lter01 := (ler01, ltr01).

Lemma ltrr : irreflexive (@ltr R).
Proof. by move=> x; rewrite /ltr lerr eqxx. Qed.
Hint Resolve ltrr.

Definition lterr := (lerr, ltrr).

Lemma ltrW x y : x < y -> x <= y.
Proof. by rewrite ler_eqVlt=> ->; rewrite orbT. Qed.
Hint Resolve ltrW.

Lemma eqr_le x y : (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP=> [->|/ler_anti //]; rewrite lerr. Qed.

Lemma ltr_anti x y : x < y < x = false.
Proof.
by rewrite !ltr_neqAle andbCA -andbA -eqr_le eq_sym; case: (x == y).
Qed.

Lemma ltr_le_anti x y : x < y <= x = false.
Proof. by rewrite ltr_neqAle -andbA -eqr_le; case: (x == y). Qed.

Lemma ler_lt_anti x y : x <= y < x = false.
Proof. by rewrite andbC ltr_le_anti. Qed.

Definition lter_anti := (=^~ eqr_le, ltr_anti, ltr_le_anti, ler_lt_anti).

Lemma ltrWN x y : x < y -> x == y = false.
Proof. by rewrite ltr_neqAle; case/andP; move/negPf=> ->. Qed.
Hint Resolve ltrWN.

Lemma ltrNW x y : y < x -> x == y = false.
Proof. by move=> hyx; rewrite eq_sym ltrWN. Qed.

Definition ltrE x y (hxy : x < y) := (hxy, (ltrWN hxy), (ltrW hxy)).

Lemma ler_lt_trans y x z : x <= y -> y < z -> x < z.
Proof.
move=> lxy; rewrite !ltr_neqAle; case/andP=> nyz lyz.
rewrite (ler_trans lxy lyz) andbT; apply: contra nyz.
by move/eqP=> eyz; rewrite eqr_le lyz -eyz.
Qed.

Lemma ltr_le_trans y x z : x < y -> y <= z -> x < z.
Proof.
rewrite !ltr_neqAle; case/andP=> nxy lxy lyz.
rewrite (ler_trans lxy lyz) andbT; apply: contra nxy.
by move/eqP=> eyz; rewrite eqr_le lxy eyz lyz.
Qed.

Lemma ltr_trans : transitive (@ltr R).
Proof. by move=> x y z /ltrW /ler_lt_trans; apply. Qed.

Hint Resolve ler_trans.
Hint Resolve ltr_trans.

Definition lter_trans y := (ler_trans, ltr_trans).
Definition lter_le_trans y x z lyz := (ler_trans^~ lyz, ltr_le_trans^~ lyz).
Definition ler_lte_trans y x z (lxy : x <= y) :=
  (@ler_trans y x z lxy, @ler_lt_trans  y x z lxy).
Definition ltr_lte_trans y x z (lxy : x < y) :=
  (@ltr_trans y x z lxy, @ltr_le_trans  y x z lxy).

Lemma lerN_po x y : x < y -> (y <= x = false).
Proof.
by move=> xy; apply: contraTF isT=> /(ltr_le_trans xy); rewrite ltrr.
Qed.

Lemma ltrN_po x y : x <= y -> (y < x = false).
Proof. by apply: contraTF=> /lerN_po->. Qed.

Lemma cpable_refl : reflexive (@cpable R).
Proof. by move=> x; rewrite /cpable lerr. Qed.

Hint Resolve cpable_refl.

Lemma cpable_sym : symmetric (@cpable R).
Proof. by move=> x y; rewrite /cpable orbC. Qed.

CoInductive le_xor_gtr (x y : R) : bool -> bool -> Set :=
  | LeNotGtr of x <= y : le_xor_gtr x y true false
  | GtrNotLe of y < x  : le_xor_gtr x y false true.

Lemma cpable_lerP x y : cpable x y -> le_xor_gtr x y (x <= y) (y < x).
Proof.
rewrite /cpable; case xy: (_ <= _); first by rewrite ltrN_po //; constructor.
rewrite /= ler_eqVlt; case yx: (_ < _); first by constructor.
by rewrite orbF=> /eqP eyx; rewrite eyx lerr in xy.
Qed.

CoInductive ltr_xor_geq (x y : R) : bool -> bool -> Set :=
  | LtrNotGeq of x < y  : ltr_xor_geq x y false true
  | GeqNotLtr of y <= x : ltr_xor_geq x y true false.

Lemma cpable_ltrP x y : cpable x y -> ltr_xor_geq x y (y <= x) (x < y).
Proof. by rewrite cpable_sym=> /cpable_lerP []; constructor. Qed.

CoInductive cparer x y : bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CparerLt of x < y : cparer x y false false true false true false
  | CparerGt of x > y : cparer x y false false false true false true
  | CparerEq of x = y : cparer x y true true true true false false.

Lemma cpable_ltrgtP x y : cpable x y -> cparer x y (y == x) (x == y)
  (x <= y) (y <= x) (x < y) (x > y) .
Proof.
move=> cxy; case: cpable_ltrP=> // hxy.
  by rewrite [_ < x]ltrN_po ltrW // ltrNW // ltrWN //; constructor.
case: cpable_lerP=> //; last by move=> lxy; rewrite ltrWN // ltrNW //; constructor.
by rewrite ler_eqVlt ltrN_po // orbF=> /eqP exy; rewrite exy eqxx; constructor.
Qed.

Lemma cpable_ltrNge x y : cpable x y -> (x < y) = ~~ (y <= x).
Proof. by case/cpable_ltrP. Qed.

Lemma cpable_lerNgt x y : cpable x y -> (x <= y) = ~~ (y < x).
Proof. by case/cpable_lerP. Qed.

Lemma cpable_neqr_lt x y : cpable x y -> (x != y) = (x < y) || (y < x).
Proof. by case/cpable_ltrgtP. Qed.

Lemma ler_cpable x y : x <= y -> cpable x y.
Proof. by rewrite /cpable=> ->. Qed.

Lemma ger_cpable x y : y <= x -> cpable x y.
Proof. by rewrite cpable_sym; apply: ler_cpable. Qed.

Lemma ltr_cpable x y : x < y -> cpable x y.
Proof. by rewrite /cpable; move/ltrW->. Qed.

Lemma gtr_cpable x y : y < x -> cpable x y.
Proof. by rewrite cpable_sym; apply: ltr_cpable. Qed.

Lemma cpableN x y : ~~ cpable x y ->
  (x == y = false) * (y == x = false)
  * (x <= y = false) * (y <= x = false)
  * (y < x = false) * (y < x = false).
Proof.
by move=> cxy; do ?split; apply: contraNF cxy;
do [by move/eqP-> | by do ?move/ltrW; move/ler_cpable; rewrite // cpable_sym].
Qed.

Lemma cpable_wlog_ler P : (forall a b, P b a -> P a b)
  -> (forall a b, a <= b -> P a b) -> forall a b : R, cpable a b -> P a b.
Proof.
move=> sP hP a b cab; wlog: a b cab / a <= b=> [hwlog|]; last exact: hP.
case: (cpable_lerP cab)=>[|/ltrW] /hwlog; first exact.
by rewrite cpable_sym=> /(_ cab) /sP.
Qed.

Lemma cpable_wlog_ltr P : (forall a, P a a) -> (forall a b, (P b a -> P a b))
  -> (forall a b, a < b -> P a b) -> forall a b : R, cpable a b -> P a b.
Proof.
move=> rP sP hP; apply: cpable_wlog_ler=> // a b.
by rewrite ler_eqVlt; case: (altP (_ =P _))=> [->|] //= _ lab; apply: hP.
Qed.

End IntegralDomainTheory.

Hint Resolve ler01.
Implicit Arguments ler01 [R].
Hint Resolve lerr.
Hint Resolve ltr01.
Implicit Arguments ltr01 [R].
Hint Resolve ltrr.
Hint Resolve ltrW.
Hint Resolve ltrWN.

Section IntegralDomainMonotonyTheory.

Variables R R' : IntegralDomain.type.
Implicit Types m n p : nat.
Implicit Types x y z : R.
Implicit Types u v w : R'.

Section RR'.

Variable D : pred R.
Variable (f : R -> R').

Lemma ltrW_wmono (mf : {wmono f :/ >%R}) : {wmono f :/ >=%R}.
Proof. by move=> x y /=; rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW //]. Qed.

Lemma ltrW_wnmono (mf : {wmono f :/~ >%R}) : {wmono f :/~ >=%R}.
Proof. by move=> x y /=; rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW //]. Qed.

Lemma wmono_inj_lt (fI : injective f) (mf : {wmono f :/ >=%R}) : {wmono f :/ >%R}.
Proof. by move=> x y /= hxy; rewrite ltr_neqAle (inj_eq fI) mf (ltrWN, ltrW). Qed.

Lemma wnmono_inj_lt (fI : injective f) (mf : {wmono f :/~ >=%R}) : {wmono f :/~ >%R}.
Proof. by move=> x y /= hxy; rewrite ltr_neqAle (inj_eq fI) mf (ltrNW, ltrW). Qed.

Lemma wmono_cpable (mf : {wmono f :/ >=%R}) : {wmono f :/ (@cpable _)}.
Proof. by move=> x y /= => /orP [] /mf /ler_cpable //; rewrite cpable_sym. Qed.

Lemma wnmono_cpable (mf : {wmono f :/~ >=%R}) : {wmono f :/ (@cpable _)}.
Proof. by move=> x y /= => /orP [] /mf /ler_cpable //; rewrite cpable_sym. Qed.

Lemma mono_cpable (mf : {mono f :/ >=%R}) : {mono f :/ (@cpable _)}.
Proof. by move=> x y /=; rewrite /cpable !mf. Qed.

Lemma nmono_cpable (mf : {mono f :/~ >=%R}) : {mono f :/ (@cpable _)}.
Proof. by move=> x y /=; rewrite /cpable !mf orbC. Qed.

Lemma mono_inj (mf : {mono f :/ >=%R}) : injective f.
Proof. by move=> x y /eqP; rewrite eqr_le !mf -eqr_le=> /eqP. Qed.

Lemma nmono_inj (mf : {mono f :/~ >=%R}) : injective f.
Proof. by move=> x y /eqP; rewrite eqr_le !mf -eqr_le=> /eqP. Qed.

Lemma lerW_mono (mf : {mono f :/ >=%R}) : {mono f :/ >%R}.
Proof.
by move=> x y /=; rewrite ltr_neqAle mf inj_eq //; apply: mono_inj.
Qed.

Lemma lerW_nmono (mf : {mono f :/~ >=%R}) : {mono f :/~ >%R}.
Proof.
move=> x y /=; rewrite ltr_neqAle mf eq_sym inj_eq //.
exact: nmono_inj.
Qed.

Lemma cpable_wmono_ler (mf : {wmono f :/ >%R})
  x y (cxy : cpable x y) : (f x <= f y) = (x <= y).
Proof. by case: (cpable_lerP cxy)=> [/ltrW_wmono|/mf /lerN_po //]; apply. Qed.

Lemma cpable_wnmono_ler (mf : {wmono f :/~ >%R})
  x y (cxy : cpable x y) : (f y <= f x) = (x <= y).
Proof. by case: (cpable_lerP cxy)=> [/ltrW_wnmono|/mf /lerN_po //]; apply. Qed.

Lemma cpable_wmono_ltr (mf : {wmono f :/ >%R})
  x y (cxy : cpable x y) : (f x < f y) = (x < y).
Proof.
case: (cpable_ltrP cxy)=> [/mf //|]; rewrite ler_eqVlt.
by case/orP=> [/eqP->|/mf /ltrW /ltrN_po //]; rewrite ltrr.
Qed.

Lemma cpable_wnmono_ltr (mf : {wmono f :/~ >%R})
  x y (cxy : cpable x y) : (f y < f x) = (x < y).
Proof.
case: (cpable_ltrP cxy)=> [/mf //|]; rewrite ler_eqVlt.
by case/orP=> [/eqP->|/mf /ltrW /ltrN_po //]; rewrite ltrr.
Qed.

(* Monotony in D *)
Lemma ltrW_wmono_in (mf : {in D &, {wmono f :/ >%R}}) : {in D &, {wmono f :/ >=%R}}.
Proof.
by move=> x y hx hy /=; rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW] //; apply.
Qed.

Lemma ltrW_wnmono_in (mf : {in D &, {wmono f :/~ >%R}}) : {in D &, {wmono f :/~ >=%R}}.
Proof.
by move=> x y hx hy /=; rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW] //; apply.
Qed.

Lemma wmono_inj_in_lt (fI : {in D &, injective f})
  (mf : {in D &, {wmono f :/ >=%R}}) : {in D &, {wmono f :/ >%R}}.
Proof.
move=> x y hx hy /= hxy; rewrite ltr_neqAle (inj_in_eq fI) //.
by rewrite mf // (ltrWN, ltrW).
Qed.

Lemma wnmono_inj_in_lt (fI : {in D &, injective f})
  (mf : {in D &, {wmono f :/~ >=%R}}) : {in D &, {wmono f :/~ >%R}}.
Proof.
move=> x y hx hy /= hxy; rewrite ltr_neqAle (inj_in_eq fI) //.
by rewrite mf // (ltrNW, ltrW).
Qed.

Lemma wmono_cpable_in (mf : {in D &, {wmono f :/ >=%R}}) :
  {in D &, {wmono f :/ (@cpable _)}}.
Proof.
by move=> x y hx hy /= => /orP [] /mf /ler_cpable //; rewrite cpable_sym; apply.
Qed.

Lemma wnmono_cpable_in (mf : {in D &, {wmono f :/~ >=%R}}) :
  {in D &, {wmono f :/ (@cpable _)}}.
Proof.
by move=> x y hx hy /= => /orP [] /mf /ler_cpable //; rewrite cpable_sym; apply.
Qed.

Lemma mono_cpable_in (mf : {in D &, {mono f :/ >=%R}}) : {in D &, {mono f :/ (@cpable _)}}.
Proof. by move=> x y hx hy /=; rewrite /cpable !mf. Qed.

Lemma nmono_cpable_in (mf : {in D &, {mono f :/~ >=%R}}) : {in D &, {mono f :/ (@cpable _)}}.
Proof. by move=> x y hx hy /=; rewrite /cpable !mf // orbC. Qed.

Lemma mono_inj_in (mf : {in D &, {mono f :/ >=%R}}) : {in D &, injective f}.
Proof. by move=> x y hx hy /= /eqP; rewrite eqr_le !mf // -eqr_le=> /eqP. Qed.

Lemma nmono_inj_in
 (mf : {in D &, {mono f :/~ >=%R}}) : {in D &, injective f}.
Proof. by move=> x y hx hy /= /eqP; rewrite eqr_le !mf // -eqr_le=> /eqP. Qed.

Lemma lerW_mono_in (mf : {in D &, {mono f :/ >=%R}}) : {in D &, {mono f :/ >%R}}.
Proof.
move=> x y hx hy /=; rewrite ltr_neqAle mf // (@inj_in_eq _ _ D) //.
exact: mono_inj_in.
Qed.

Lemma lerW_nmono_in (mf : {in D &, {mono f :/~ >=%R}}) : {in D &, {mono f :/~ >%R}}.
Proof.
move=> x y hx hy /=; rewrite ltr_neqAle mf // eq_sym (@inj_in_eq _ _ D) //.
exact: nmono_inj_in.
Qed.

Lemma cpable_wmono_in_ler (mf : {in D &, {wmono f :/ >%R}})
  x y (hx : x \in D) (hy : y \in D) (cxy : cpable x y) : (f x <= f y) = (x <= y).
Proof. by case: (cpable_lerP cxy)=> [/ltrW_wmono_in|/mf /lerN_po //]; apply. Qed.

Lemma cpable_wnmono_in_ler (mf : {in D &, {wmono f :/~ >%R}})
  x y (hx : x \in D) (hy : y \in D) (cxy : cpable x y) : (f y <= f x) = (x <= y).
Proof. by case: (cpable_lerP cxy)=> [/ltrW_wnmono_in|/mf /lerN_po //]; apply. Qed.

Lemma cpable_wmono_in_ltr (mf : {in D &, {wmono f :/ >%R}})
  x y (hx : x \in D) (hy : y \in D) (cxy : cpable x y) : (f x < f y) = (x < y).
Proof.
case: (cpable_ltrP cxy)=> [/mf //|]; first by apply.
rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW /ltrN_po //]; last exact.
by rewrite ltrr.
Qed.

Lemma cpable_wnmono_in_ltr (mf : {in D &, {wmono f :/~ >%R}})
  x y (hx : x \in D) (hy : y \in D) (cxy : cpable x y) : (f y < f x) = (x < y).
Proof.
case: (cpable_ltrP cxy)=> [/mf //|]; first by apply.
rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW /ltrN_po //]; last exact.
by rewrite ltrr.
Qed.

End RR'.

Section natR.

Variable (f : nat -> R).

Lemma ltn_ltrW_wmono (mf : {wmono f : m n / (m < n)%N >-> m < n}) :
  {wmono f : m n / (m <= n)%N >-> m <= n}.
Proof. by move=> m n /=; rewrite leq_eqVlt=> /orP [/eqP->|/mf /ltrW //]. Qed.

Lemma ltn_ltrW_wnmono (mf : {wmono f : m n / (n < m)%N >-> m < n}) :
  {wmono f : m n / (n <= m)%N >-> m <= n}.
Proof. by move=> m n /=; rewrite leq_eqVlt=> /orP [/eqP->|/mf /ltrW //]. Qed.

Lemma wmono_inj_ltn_lt (fI : injective f) (mf : {wmono f : m n / (m <= n)%N >-> m <= n}) :
  {wmono f : m n / (m < n)%N >-> m < n}.
Proof.
by move=> m n /= hmn; rewrite ltr_neqAle (inj_eq fI) mf ?neq_ltn ?hmn // ltnW.
Qed.

Lemma wnmono_inj_ltn_lt (fI : injective f) (mf : {wmono f : m n / (n <= m)%N >-> m <= n}) :
  {wmono f : m n / (n < m)%N >-> m < n}.
Proof.
by  move=> m n /= hmn; rewrite ltr_neqAle (inj_eq fI) mf ?neq_ltn ?hmn ?orbT // ltnW.
Qed.

Lemma leq_mono_inj (mf : {mono f : m n / (m <= n)%N >-> m <= n}) : injective f.
Proof. by move=> m n /eqP; rewrite eqr_le !mf -eqn_leq=> /eqP. Qed.

Lemma leq_nmono_inj (mf : {mono f : m n / (n <= m)%N >-> m <= n}) : injective f.
Proof. by move=> m n /eqP; rewrite eqr_le !mf -eqn_leq=> /eqP. Qed.

Lemma leq_lerW_mono (mf : {mono f : m n / (m <= n)%N >-> m <= n}) :
  {mono f : m n / (m < n)%N >-> m < n}.
Proof.
move=> m n /=; rewrite ltr_neqAle mf inj_eq ?ltn_neqAle //.
exact: leq_mono_inj.
Qed.

Lemma leq_lerW_nmono (mf : {mono f : m n / (n <= m)%N >-> m <= n}) :
  {mono f : m n / (n < m)%N >-> m < n}.
Proof.
move=> x y /=; rewrite ltr_neqAle mf eq_sym inj_eq ?ltn_neqAle //.
exact: leq_nmono_inj.
Qed.

Lemma wmono_leq_mono (mf : {wmono f : m n / (m < n)%N >-> m < n}) :
  {mono f : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> m n /=; case: leqP; last by move=> /mf /lerN_po.
by rewrite leq_eqVlt=> /orP [/eqP->|/mf /ltrW //]; rewrite lerr.
Qed.

Lemma wnmono_leq_mono (mf : {wmono f : m n / (n < m)%N >-> m < n}) :
  {mono f : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> m n /=; case: leqP; last by move=> /mf /lerN_po.
by rewrite leq_eqVlt=> /orP [/eqP->|/mf /ltrW //]; rewrite lerr.
Qed.

Lemma leq_cpable_wmono (mf : {wmono f : m n / (m <= n)%N >-> m <= n}) m n :
  cpable (f m) (f n).
Proof.
by case/orP: (leq_total m n)=> /mf /ler_cpable //; rewrite cpable_sym.
Qed.

Lemma leq_cpable_wnmono (mf : {wmono f : m n / (n <= m)%N >-> m <= n}) m n :
  cpable (f m) (f n).
Proof.
by case/orP: (leq_total m n)=> /mf /ler_cpable //; rewrite cpable_sym.
Qed.

End natR.

End IntegralDomainMonotonyTheory.

Section IntegralDomainOperationTheory.
(* Comparision and opposite *)

Variable R : IntegralDomain.type.
Implicit Types x y z t : R.

Lemma oppr_mono : {mono -%R :/~ (>=%R : rel R)}.
Proof. by move=> x y; rewrite -subr_ge0 opprK addrC subr_ge0. Qed.
Hint Resolve oppr_mono.

Lemma ler_opp2 x y : (- x <= - y) = (y <= x). Proof. done. Qed.

Lemma ltr_opp2 x y : (- x < - y) = (y < x). Proof. by rewrite lerW_nmono. Qed.

Definition lter_opp2 := (ler_opp2, ltr_opp2).

Lemma ler_oppr x y : (x <= - y) = (y <= - x).
Proof. by rewrite (mono2RL (@opprK _) oppr_mono). Qed.

Lemma ltr_oppr x y : (x < - y) = (y < - x).
Proof. by rewrite (mono2RL (@opprK _) (lerW_nmono _)). Qed.

Definition lter_oppr := (ler_oppr, ltr_oppr).

Lemma ler_oppl x y : (- x <= y) = (- y <= x).
Proof. by rewrite (mono2LR (@opprK _) oppr_mono). Qed.

Lemma ltr_oppl x y : (- x < y) = (- y < x).
Proof. by rewrite (mono2LR (@opprK _) (lerW_nmono _)). Qed.

Definition lter_oppl := (ler_oppl, ltr_oppl).

Lemma oppr_ge0 x : (0 <= - x) = (x <= 0).
Proof. by rewrite lter_oppr oppr0. Qed.

Lemma oppr_gt0 x : (0 < - x) = (x < 0).
Proof. by rewrite lter_oppr oppr0. Qed.

Definition oppr_gte0 := (oppr_ge0, oppr_gt0).

Lemma oppr_le0 x : (- x <= 0) = (0 <= x).
Proof. by rewrite lter_oppl oppr0. Qed.

Lemma oppr_lt0 x : (- x < 0) = (0 < x).
Proof. by rewrite lter_oppl oppr0. Qed.

Definition oppr_lte0 := (oppr_le0, oppr_lt0).
Definition oppr_cp0 := (oppr_gte0, oppr_lte0).
Definition lter_oppE := (oppr_cp0, lter_opp2).

Lemma ge0_cp x : 0 <= x -> (- x <= 0) * (- x <= x).
Proof. by move=> hx; rewrite oppr_cp0 hx (@ler_trans _ 0) ?oppr_cp0. Qed.

Lemma gt0_cp x : 0 < x ->
 (0 <= x) * (- x <= 0) * (- x <= x) * (- x < 0) * (- x < x).
Proof.
move=> hx; move: (ltrW hx)=> hx'; rewrite !ge0_cp hx' //.
by rewrite oppr_cp0 hx // (@ltr_trans _ 0) ?oppr_cp0.
Qed.

Lemma le0_cp x : x <= 0 -> (0 <= - x) * (x <= - x).
Proof. by move=> hx; rewrite oppr_cp0 hx (@ler_trans _ 0) ?oppr_cp0. Qed.

Lemma lt0_cp x : x < 0 ->
  (x <= 0) * (0 <= - x) * (x <= - x) * (0 < - x) * (x < - x).
Proof.
move=> hx; move: (ltrW hx)=> hx'; rewrite !le0_cp // hx'.
by rewrite oppr_cp0 hx // (@ltr_trans _ 0) ?oppr_cp0.
Qed.

(* Monotony of addition *)
Lemma ler_add2l x : {mono +%R x :/ (>=%R : rel R)}.
Proof.
by move=> y z; rewrite -subr_ge0 oppr_add addrAC addNKr addrC subr_ge0.
Qed.

Lemma ler_add2r x : {mono +%R^~ x :/ (>=%R : rel R)}.
Proof. by move=> y z /=; rewrite ![_ + x]addrC ler_add2l. Qed.

Lemma ltr_add2r z x y : (x + z < y + z) = (x < y).
Proof. by rewrite (lerW_mono (ler_add2r _)). Qed.

Lemma ltr_add2l z x y : (z + x < z + y) = (x < y).
Proof. by rewrite (lerW_mono (ler_add2l _)). Qed.

Definition lter_add2r := (ler_add2r, ltr_add2r).
Definition lter_add2l := (ler_add2l, ltr_add2l).
Definition lter_add2 := (lter_add2l, lter_add2r).

(* Comparision to 0 of a difference *)
Lemma subr_le0  x y : (y - x <= 0) = (y <= x).
Proof. by rewrite -subr_ge0 oppr_sub add0r subr_ge0. Qed.

Lemma subr_gt0  x y : (0 < y - x) = (x < y).
Proof. by rewrite ltr_neqAle subr_ge0 eq_sym subr_eq0 eq_sym. Qed.

Lemma subr_lt0  x y : (y - x < 0) = (y < x).
Proof. by rewrite ltr_neqAle subr_le0 subr_eq0. Qed.

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).

(* Addition, substraction and transitivity *)
Lemma ler_add x y z t : x <= y -> z <= t -> x + z <= y + t.
Proof. by move=> lxy lzt; rewrite (@ler_trans _ (y + z)) ?lter_add2. Qed.

Lemma ler_lt_add x y z t : x <= y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@ler_lt_trans _ (y + z)) ?lter_add2. Qed.

Lemma ltr_le_add x y z t : x < y -> z <= t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite (@ltr_le_trans _ (y + z)) ?lter_add2. Qed.

Lemma ltr_add x y z t : x < y -> z < t -> x + z < y + t.
Proof. by move=> lxy lzt; rewrite ltr_le_add // ltrW. Qed.

Lemma ler_sub x y z t : x <= y -> t <= z -> x - z <= y - t.
Proof. by move=> lxy ltz; rewrite ler_add // lter_opp2. Qed.

Lemma ler_lt_sub x y z t : x <= y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ler_lt_add // lter_opp2. Qed.

Lemma ltr_le_sub x y z t : x < y -> t <= z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltr_le_add // lter_opp2. Qed.

Lemma ltr_sub x y z t : x < y -> t < z -> x - z < y - t.
Proof. by move=> lxy lzt; rewrite ltr_add // lter_opp2. Qed.

Lemma ler_subl_addr x y z : (x - y <= z) = (x <= z + y).
Proof. by rewrite (mono2LR (addrK _) (ler_add2r _)). Qed.

Lemma ltr_subl_addr x y z : (x - y < z) = (x < z + y).
Proof. by rewrite (mono2LR (addrK _) (ltr_add2r _)). Qed.

Lemma ler_subr_addr x y z : (x <= y - z) = (x + z <= y).
Proof. by rewrite (mono2LR (addrNK _) (ler_add2r _)). Qed.

Lemma ltr_subr_addr x y z : (x < y - z) = (x + z < y).
Proof. by rewrite (mono2LR (addrNK _) (ltr_add2r _)). Qed.

Definition lter_subl_addr := (ler_subl_addr, ltr_subl_addr).
Definition lter_subr_addr := (ler_subr_addr, ltr_subr_addr).
Definition lter_sub_addr := (lter_subr_addr, lter_subl_addr).

Lemma ler_subl_addl x y z : (x - y <= z) = (x <= y + z).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ltr_subl_addl x y z : (x - y < z) = (x < y + z).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ler_subr_addl x y z : (x <= y - z) = (z + x <= y).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ltr_subr_addl x y z : (x < y - z) = (z + x < y).
Proof. by rewrite lter_sub_addr addrC. Qed.

Definition lter_subl_addl := (ler_subl_addl, ltr_subl_addl).
Definition lter_subr_addl := (ler_subr_addl, ltr_subr_addl).
Definition lter_sub_addl := (lter_subr_addl, lter_subl_addl).

Lemma ler_addl x y : (x <= x + y) = (0 <= y).
Proof. by rewrite -{1}[x]addr0 lter_add2l. Qed.

Lemma ltr_addl x y : (x < x + y) = (0 < y).
Proof. by rewrite -{1}[x]addr0 lter_add2l. Qed.

Lemma ler_addr x y : (x <= y + x) = (0 <= y).
Proof. by rewrite -{1}[x]add0r lter_add2r. Qed.

Lemma ltr_addr x y : (x < y + x) = (0 < y).
Proof. by rewrite -{1}[x]add0r lter_add2r. Qed.

Definition lter_addr := (ler_addr, ltr_addr).
Definition lter_addl := (ler_addl, ltr_addl).
Definition lter_add := (lter_addr, lter_addl).

Lemma ger_addl x y : (x + y <= x) = (y <= 0).
Proof. by rewrite -{2}[x]addr0 lter_add2l. Qed.

Lemma gtr_addl x y : (x + y < x) = (y < 0).
Proof. by rewrite -{2}[x]addr0 lter_add2l. Qed.

Lemma ger_addr x y : (y + x <= x) = (y <= 0).
Proof. by rewrite -{2}[x]add0r lter_add2r. Qed.

Lemma gtr_addr x y : (y + x < x) = (y < 0).
Proof. by rewrite -{2}[x]add0r lter_add2r. Qed.

Definition gter_addr := (ger_addr, gtr_addr).
Definition gter_addl := (ger_addl, gtr_addl).
Definition gter_add := (gter_addr, gter_addl).
Definition cpr_add := (gter_add, lter_add).

(* Addition with left member we know positive/negative *)
Lemma ler_paddl y x z : 0 <= x -> y <= z -> y <= x + z.
Proof. by move=> *; rewrite -[y]add0r ler_add. Qed.

Lemma ltr_paddl y x z : 0 <= x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ler_lt_add. Qed.

Lemma ltr_spaddl y x z : 0 < x -> y <= z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltr_le_add. Qed.

Lemma ltr_spsaddl y x z : 0 < x -> y < z -> y < x + z.
Proof. by move=> *; rewrite -[y]add0r ltr_add. Qed.

Lemma ler_naddl y x z : x <= 0 -> y <= z -> x + y <= z.
Proof. by move=> *; rewrite -[z]add0r ler_add. Qed.

Lemma ltr_naddl y x z : x <= 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ler_lt_add. Qed.

Lemma ltr_snaddl y x z : x < 0 -> y <= z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltr_le_add. Qed.

Lemma ltr_snsaddl y x z : x < 0 -> y < z -> x + y < z.
Proof. by move=> *; rewrite -[z]add0r ltr_add. Qed.

(* Addition with right member we know positive/negative *)
Lemma ler_paddr y x z : 0 <= x -> y <= z -> y <= z + x.
Proof. by move=> *; rewrite [_ + x]addrC ler_paddl. Qed.

Lemma ltr_paddr y x z : 0 <= x -> y < z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltr_paddl. Qed.

Lemma ltr_spaddr y x z : 0 < x -> y <= z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltr_spaddl. Qed.

Lemma ltr_spsaddr y x z : 0 < x -> y < z -> y < z + x.
Proof. by move=> *; rewrite [_ + x]addrC ltr_spsaddl. Qed.

Lemma ler_naddr y x z : x <= 0 -> y <= z -> y + x <= z.
Proof. by move=> *; rewrite [_ + x]addrC ler_naddl. Qed.

Lemma ltr_naddr y x z : x <= 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltr_naddl. Qed.

Lemma ltr_snaddr y x z : x < 0 -> y <= z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltr_snaddl. Qed.

Lemma ltr_snsaddr y x z : x < 0 -> y < z -> y + x < z.
Proof. by move=> *; rewrite [_ + x]addrC ltr_snsaddl. Qed.

(* x and y have se same sign and their sum is null *)
Lemma paddr_eq0 (x y : R) : 0 <= x -> 0 <= y ->
  (x + y == 0) = (x == 0) && (y == 0).
Proof.
rewrite ler_eqVlt; case/orP=> hx; rewrite [x == 0]eq_sym.
  by rewrite hx -(eqP hx) add0r.
rewrite (ltrWN hx) /= => hy; rewrite eq_sym; apply: ltrWN.
exact: ltr_spaddl.
Qed.

Lemma naddr_eq0 (x y : R) (hx : x <= 0) (hy : y <= 0) :
  (x + y == 0) = (x == 0) && (y == 0).
Proof. by rewrite -oppr_eq0 oppr_add paddr_eq0 ?oppr_cp0 // !oppr_eq0. Qed.

Lemma addr_ss_eq0 (x y : R) : (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0)
 -> (x + y == 0) = (x == 0) && (y == 0).
Proof. by case/orP=> /andP []; [apply: paddr_eq0|apply: naddr_eq0]. Qed.

(* big ops and ler*)
Lemma sumr_ge0 I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> (0 <= F i)) -> 0 <= \sum_(i <- r | P i) (F i).
Proof. exact: (big_ind _ _ (@ler_paddl 0)). Qed.

Lemma ler_sum I (r : seq I) (P : pred I) (F G : I -> R) :
  (forall i, P i -> F i <= G i) ->
  (\sum_(i <- r | P i) F i) <= \sum_(i <- r | P i) G i.
Proof. exact: (big_ind2 _ (lerr _) ler_add). Qed.

Lemma sumr_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof.
elim: r=> [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
by case: ifP=> pa /=; rewrite ?paddr_eq0 ?ihr ?hr // sumr_ge0.
Qed.

(* natmul and ler/ltr *)

Lemma ltr_wmuln2r x y n (hxy : x < y) : x *+ n < y *+ n = (n != 0%N).
Proof.
case: n; rewrite ?mulr0n ?ltrr //.
by elim=> [|n IH] //; rewrite ![_ *+ _.+2]mulrS ltr_add.
Qed.

Lemma ltr_wpmuln2r n (hn : (0 < n)%N) : {wmono (@GRing.natmul R)^~ n :/ >%R}.
Proof. by move=> x y xy; case: n hn=> [//|n _]; rewrite ltr_wmuln2r. Qed.

Lemma ler_wmuln2r n : {wmono (@GRing.natmul R)^~ n :/ >=%R}.
Proof. by move=> x y xy; elim: n => [|n ihn] //; rewrite !mulrS ler_add. Qed.

Lemma mulrn_wge0 x n : 0 <= x -> 0 <= x *+ n.
Proof. by move=> /(ler_wmuln2r n); rewrite mul0rn. Qed.

Lemma cpable_mulrn_ge0 n (hn : (0 < n)%N) x (cx : cpable 0 x) :
  (0 <= x *+ n) = (0 <= x).
Proof. by rewrite -{1}(mul0rn _ n) (cpable_wmono_ler (ltr_wpmuln2r _)). Qed.

Lemma mulrn_wle0 x n : x <= 0 -> x *+ n <= 0.
Proof. by move=> /(ler_wmuln2r n); rewrite mul0rn. Qed.

Lemma cpable_mulrn_le0 n (hn : (0 < n)%N) x (cx : cpable x 0) :
  (x *+ n <= 0) = (x <= 0).
Proof. by rewrite -{1}(mul0rn _ n) (cpable_wmono_ler (ltr_wpmuln2r _)). Qed.

Lemma ler_wpmuln2l x (hx : 0 <= x) :
  {wmono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof.
by move=> m n hmn; rewrite -(subnK hmn) mulrn_addr ler_paddl // mulrn_wge0.
Qed.

Lemma ler_wnmuln2l x (hx : x <= 0) :
  {wmono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> m n hmn /=; rewrite -ler_opp2 -!mulNrn ler_wpmuln2l // oppr_cp0.
Qed.

Lemma mulrn_wgt0 x n : 0 < x -> 0 < x *+ n = (n != 0%N).
Proof. by move=> /(ltr_wmuln2r n); rewrite mul0rn. Qed.

Lemma mulrn_wlt0 x n : x < 0 -> x *+ n < 0 = (n != 0%N).
Proof. by move=> /(ltr_wmuln2r n); rewrite mul0rn. Qed.

Lemma ler_pmuln2l x (hx : 0 < x) :
  {mono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> m n /=; case: leqP => hmn; first by rewrite ler_wpmuln2l // ltrW.
rewrite -(subnK (ltnW hmn)) mulrn_addr ger_addr lerN_po //.
by rewrite mulrn_wgt0 // subn_eq0 -ltnNge.
Qed.

Lemma ltr_pmuln2l x (hx : 0 < x) :
  {mono (@GRing.natmul R x) : m n / (m < n)%N >-> m < n}.
Proof. exact: leq_lerW_mono (ler_pmuln2l _). Qed.

Lemma ler_nmuln2l x (hx : x < 0) :
  {mono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> m n /=; rewrite -oppr_mono -!mulNrn ler_pmuln2l // oppr_gt0.
Qed.

Lemma ltr_nmuln2l x (hx : x < 0) :
  {mono (@GRing.natmul R x) : m n / (n < m)%N >-> m < n}.
Proof. exact: leq_lerW_nmono (ler_nmuln2l _). Qed.

Lemma ler0n n : 0 <= n%:R :> R. Proof. by rewrite mulrn_wge0. Qed.
Hint Resolve ler0n.

Lemma ltr0n n : 0 < n%:R :> R = (n != 0%N).
Proof. by rewrite mulrn_wgt0. Qed.

Lemma ltr0Sn n : 0 < (n.+1)%:R :> R. Proof. by rewrite ltr0n. Qed.
Hint Resolve ltr0Sn.

Lemma cpable0n n : @cpable R 0 n%:R. Proof. by rewrite ler_cpable. Qed.
Hint Resolve cpable0n.

Lemma cpablen0 n : @cpable R n%:R 0. Proof. by rewrite cpable_sym. Qed.
Hint Resolve cpablen0.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0%N).
Proof. by rewrite cpable_lerNgt // ltr0n negbK. Qed.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Proof. by rewrite cpable_ltrNge // ler0n. Qed.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Proof. by case: n=> [|n]; rewrite ?mulr0n ?eqxx // ltrNW. Qed.

Lemma char_po : [char R] =i pred0.
Proof. by case=> // p /=; rewrite !inE pnatr_eq0 andbF. Qed.

Lemma mulrn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Proof. by rewrite -mulr_natl mulf_eq0 pnatr_eq0. Qed.

Lemma mulrIn x : x != 0 -> injective (GRing.natmul x).
Proof.
move=> hx m n.
case: (ltngtP m n)=> // hmn; rewrite -(subnK (ltnW hmn)) mulrn_addr.
  move/(canLR (addrK _))=> /eqP; rewrite subrr eq_sym mulrn_eq0.
  by rewrite (negPf hx) orbF=> /eqP ->.
move/(canRL (addrK _))=> /eqP; rewrite subrr mulrn_eq0.
by rewrite (negPf hx) orbF=> /eqP ->.
Qed.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Proof. by rewrite ler_pmuln2l. Qed.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Proof. by rewrite ltr_pmuln2l. Qed.

Lemma cpablen m n : @cpable R n%:R m%:R.
Proof. by rewrite /cpable !ler_nat leq_total. Qed.
Hint Resolve cpablen.

Lemma ltrN10 : -1 < 0 :> R. Proof. by rewrite oppr_lt0. Qed.
Lemma lerN10 : -1 <= 0 :> R. Proof. by rewrite oppr_le0. Qed.
Lemma ltr10 : 1 < 0 :> R = false. Proof. by rewrite ltrN_po. Qed.
Lemma ler10 : 1 <= 0 :> R = false. Proof. by rewrite lerN_po. Qed.
Lemma ltr0N1 : 0 < -1 :> R = false. Proof. by rewrite ltrN_po // lerN10. Qed.
Lemma ler0N1 : 0 <= -1 :> R = false. Proof. by rewrite lerN_po // ltrN10. Qed.

(* mulr and ler/ltr *)
Lemma mulr_gt0 x y : 0 < x -> 0 < y -> 0 < (x * y).
Proof.
move=> px py; rewrite ltr_neqAle mulr_ge0 ?ltrW // eq_sym andbT.
by rewrite mulf_neq0 // eq_sym ltrWN.
Qed.

Definition mulr_gte0 := (mulr_ge0, mulr_gt0).

Lemma mulr_le0 x y : x <= 0 -> y <= 0 -> 0 <= (x * y).
Proof. by move=> hx hy; rewrite -mulrNN mulr_gte0 ?oppr_gte0. Qed.

Lemma mulr_lt0 x y : x < 0 -> y < 0 -> 0 < (x * y).
Proof. by move=> hx hy; rewrite -mulrNN mulr_gte0 ?oppr_gte0. Qed.

Definition mulr_lte0 := (mulr_le0, mulr_lt0).

Lemma mulr_ge0_le0 x y : 0 <= x -> y <= 0 -> (x * y) <= 0.
Proof. by move=> *; rewrite -oppr_gte0 -mulrN mulr_gte0 ?oppr_gte0. Qed.

Lemma mulr_gt0_lt0 x y : 0 < x -> y < 0 -> (x * y) < 0.
Proof. by move=> *; rewrite -oppr_gte0 -mulrN mulr_gte0 ?oppr_gte0. Qed.

Definition mulr_gte0_lte0 := (mulr_ge0_le0, mulr_gt0_lt0).

Lemma mulr_le0_ge0 x y : x <= 0 -> 0 <= y -> (x * y) <= 0.
Proof. by move=> *; rewrite -oppr_gte0 -mulNr mulr_gte0 ?oppr_gte0. Qed.

Lemma mulr_lt0_gt0 x y : x < 0 -> 0 < y -> (x * y) < 0.
Proof. by move=> *; rewrite -oppr_gte0 -mulNr mulr_gte0 ?oppr_gte0. Qed.

Definition mulr_lte0_gte0 := (mulr_le0_ge0, mulr_lt0_gt0).

Definition mulr_gte0_cp0 := (mulr_gte0, mulr_gte0_lte0).
Definition mulr_lte0_cp0 := (mulr_lte0, mulr_lte0_gte0).

Lemma ler_wpmul2l x (hx : 0 <= x) : {wmono *%R x :/ >=%R}.
Proof. by move=> /= *; rewrite -subr_ge0 -mulr_subr mulr_ge0 // subr_ge0. Qed.

Lemma ltr_wpmul2l x (hx : 0 < x) : {wmono *%R x :/ >%R}.
Proof.
move=> /= *; rewrite ltr_neqAle eq_sym ler_wpmul2l // ?ltrW //.
by rewrite (inj_eq (mulfI _)) ltrNW.
Qed.

Definition lter_wpmul2l := (ler_wpmul2l, ltr_wpmul2l).

Lemma ler_wpmul2r x (hx : 0 <= x) : {wmono *%R^~ x :/ >=%R}.
Proof. by move=> /= *; rewrite ![_ * x]mulrC lter_wpmul2l. Qed.

Lemma ltr_wpmul2r x (hx : 0 < x) : {wmono *%R^~ x :/ >%R}.
Proof. by move=> /= *; rewrite ![_ * x]mulrC lter_wpmul2l. Qed.

Definition lter_wpmul2r := (ler_wpmul2r, ltr_wpmul2r).
Definition lter_wpmul := (lter_wpmul2l, lter_wpmul2r).

Lemma ler_wnmul2l x (hx : x <= 0) : {wmono *%R x :/~ >=%R}.
Proof. by move=> /= *; rewrite -![x * _]mulrNN lter_wpmul ?lter_oppE. Qed.

Lemma ltr_wnmul2l  x (hx : x < 0) : {wmono *%R x :/~ >%R}.
Proof. by move=> /= *; rewrite -![x * _]mulrNN lter_wpmul ?lter_oppE. Qed.

Definition lter_wnmul2l := (ler_wnmul2l, ltr_wnmul2l).

Lemma ler_wnmul2r x (hx : x <= 0) : {wmono *%R^~ x :/~ >=%R}.
Proof. by move=> /= *; rewrite -![_ * x]mulrNN lter_wpmul ?lter_oppE. Qed.

Lemma ltr_wnmul2r x (hx : x < 0) : {wmono *%R^~ x :/~ >%R}.
Proof. by move=> /= *; rewrite -![_ * x]mulrNN lter_wpmul ?lter_oppE. Qed.

Definition lter_wnmul2r := (ler_wnmul2r, ltr_wnmul2r).
Definition lter_wnmul := (lter_wnmul2l, lter_wnmul2r).

(* ler/ltr and multiplication between a positive/negative
   and a exterior (1 <= _) or interior (0 <= _ <= 1) *)
Lemma ler_pemull x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wpmul2r. Qed.

Lemma ltr_pemull x y : 1 < x -> 0 < y -> y < x * y.
Proof. by move=> hx hy; rewrite -{1}[y]mul1r ltr_wpmul2r. Qed.

Definition lter_pemull := (ler_pemull, ltr_pemull).

Lemma ler_nemull x y : 1 <= x -> y <= 0 -> x * y <= y.
Proof. by move=> hx hy; rewrite -{2}[y]mul1r ler_wnmul2r. Qed.

Lemma ltr_nemull x y : 1 < x -> y < 0 -> x * y < y.
Proof. by move=> hx hy; rewrite -{2}[y]mul1r ltr_wnmul2r. Qed.

Definition lter_nemull := (ler_nemull, ltr_nemull).
Definition lter_emull := (lter_pemull, lter_nemull).

Lemma ler_pemulr x y : 1 <= x -> 0 <= y -> y <= y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ler_wpmul2l. Qed.

Lemma ltr_pemulr x y : 1 < x -> 0 < y -> y < y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ltr_wpmul2l. Qed.

Definition lter_pemulr := (ler_pemulr, ltr_pemulr).

Lemma ler_nemulr x y : 1 <= x -> y <= 0 -> y * x <= y.
Proof. by move=> hx hy; rewrite -{2}[y]mulr1 ler_wnmul2l. Qed.

Lemma ltr_nemulr x y : 1 < x -> y < 0 -> y * x < y.
Proof. by move=> hx hy; rewrite -{2}[y]mulr1 ltr_wnmul2l. Qed.

Definition lter_nemulr := (ler_nemulr, ltr_nemulr).
Definition lter_emulr := (lter_pemulr, lter_nemulr).

Lemma ler_pimull x y : x <= 1 -> 0 <= y -> x * y <= y.
Proof. by move=> hx hy; rewrite -{2}[y]mul1r ler_wpmul2r. Qed.

Lemma ltr_pimull x y : x < 1 -> 0 < y -> x * y < y.
Proof. by move=> hx hy; rewrite -{2}[y]mul1r ltr_wpmul2r. Qed.

Definition lter_pimull := (ler_pimull, ltr_pimull).

Lemma ler_nimull x y : x <= 1 -> y <= 0 -> y <= x * y.
Proof. by move=> hx hy; rewrite -{1}[y]mul1r ler_wnmul2r. Qed.

Lemma ltr_nimull x y : x < 1 -> y < 0 -> y < x * y.
Proof. by move=> hx hy; rewrite -{1}[y]mul1r ltr_wnmul2r. Qed.

Definition lter_nimull := (ler_nimull, ltr_nimull).
Definition lter_imull := (lter_nimull, lter_pimull).

Lemma ler_pimulr x y : x <= 1 -> 0 <= y -> y * x <= y.
Proof. by move=> hx hy; rewrite -{2}[y]mulr1 ler_wpmul2l. Qed.

Lemma ltr_pimulr x y : x < 1 -> 0 < y -> y * x < y.
Proof. by move=> hx hy; rewrite -{2}[y]mulr1 ltr_wpmul2l. Qed.

Definition lter_pimulr := (ler_pimulr, ltr_pimulr).

Lemma ler_nimulr x y : x <= 1 -> y <= 0 -> y <= y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ler_wnmul2l. Qed.

Lemma ltr_nimulr x y : x < 1 -> y < 0 -> y < y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ltr_wnmul2l. Qed.

Definition lter_nimulr := (ler_nimulr, ltr_nimulr).
Definition lter_imulr := (lter_pimulr, lter_nimulr).

Lemma mulr_ile1 x y : 0 <= x -> 0 <= y -> x <= 1 -> y <= 1 -> x * y <= 1.
Proof. by move=> *; rewrite (@ler_trans _ y) ?ler_pimull. Qed.

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Proof. by move=> *; rewrite (@ler_lt_trans _ y) ?ler_pimull // ltrW. Qed.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y (l1x : 1 <= x) (l1y : 1 <= y) : 1 <= x * y.
Proof. by rewrite (@ler_trans _ y) ?ler_pemull // (ler_trans ler01). Qed.

Lemma mulr_egt1 x y (l1x : 1 < x) (l1y : 1 < y) : 1 < x * y.
Proof. by rewrite (@ltr_trans _ y) ?ltr_pemull // (ltr_trans ltr01). Qed.

Definition mulr_egte1 := (mulr_ege1, mulr_egt1).
Definition mulr_cp1 := (mulr_ilte1, mulr_egte1).

(* ler and exprn *)
Lemma exprn_ge0 n x (hx : 0 <= x) : (0 <= x ^+ n).
Proof. by elim: n=> [|n ihn]; rewrite ?ler01 // exprS mulr_ge0 ?ihn. Qed.

Lemma exprn_gt0 n x (hx : 0 < x) : (0 < x ^+ n).
Proof. by elim: n=> [|n ihn]; rewrite ?ltr01 // exprS mulr_gt0 ?ihn. Qed.

Definition exprn_gte0 := (exprn_ge0, exprn_gt0).

Lemma exprn_ile1 n x (x0 : 0 <= x) (x1 : x <= 1) : x ^+ n <= 1.
Proof. by elim: n=> [|*]; rewrite ?expr0 // exprS mulr_ile1 ?exprn_ge0. Qed.

Lemma exprn_ilt1 n x (x0 : 0 <= x) (x1 : x < 1) : x ^+ n < 1 = (n != 0%N).
Proof.
case: n; [by rewrite eqxx ltrr | elim=> [|n ihn]; first by rewrite expr1].
by rewrite exprS mulr_ilt1 // exprn_ge0.
Qed.

Definition exprn_ilte1:= (exprn_ile1, exprn_ilt1).

Lemma exprn_ege1 n x (x1 : 1 <= x) : 1 <= x ^+ n.
Proof. by elim: n=> [|n ihn]; rewrite ?expr0 // exprS mulr_ege1. Qed.

Lemma exprn_egt1 n x (x1 : 1 < x) : 1 < x ^+ n = (n != 0%N).
Proof.
case: n; [by rewrite eqxx ltrr | elim=> [|n ihn]; first by rewrite expr1].
by rewrite exprS mulr_egt1 // exprn_ge0.
Qed.

Definition exprn_egte1 := (exprn_ege1, exprn_egt1).
Definition exprn_cp1 := (exprn_ilte1, exprn_egte1).


Lemma ler_iexprS x n (x0 : 0 <= x) (x1 : x <= 1) : x ^+ n.+1 <= x.
Proof. by rewrite exprS lter_imulr // exprn_ile1. Qed.

Lemma ltr_iexprS x n (x0 : 0 < x) (x1 : x < 1) : x ^+ n.+1 < x = (n != 0%N).
Proof.
by case: n=> [//|n]; rewrite ?ltrr // exprS ltr_pimulr ?exprn_ilt1 // ltrW.
Qed.

Definition lter_iexprS := (ler_iexprS, ltr_iexprS).

Lemma ler_eexprS x n (x1 : 1 <= x) : x <= x ^+ n.+1.
Proof. by rewrite exprS lter_emulr ?(ler_trans _ x1) ?ler01// exprn_ege1. Qed.

Lemma ltr_eexprS x n (x1 : 1 < x) : x < x ^+ n.+1 = (n != 0%N).
Proof.
case: n=> [//|n]; rewrite ?ltrr // exprS ltr_pemulr ?exprn_egt1 //.
by rewrite (ltr_trans _ x1) // ltr01.
Qed.

Definition lter_eexprS := (ler_eexprS, ltr_eexprS).
Definition lter_exprS := (lter_iexprS, lter_eexprS).

Lemma ler_wiexpn2l x (x0 : 0 <= x) (x1 : x <= 1) :
  {wmono (GRing.exp x) : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> m n /= hmn.
by rewrite -(subnK hmn) exprn_addr ler_pimull ?(exprn_ge0, exprn_ile1).
Qed.

Lemma ler_weexpn2l x (x1 : 1 <= x) :
  {wmono (GRing.exp x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> m n /= hmn; rewrite -(subnK hmn) exprn_addr.
by rewrite ler_pemull ?(exprn_ge0, exprn_ege1) // (ler_trans _ x1) ?ler01.
Qed.

Lemma cpable_iexpn2l x m n (x0 : 0 <= x) (x1 : x <= 1) : cpable (x ^+ m) (x ^+ n).
Proof. by rewrite leq_cpable_wnmono //; apply: ler_wiexpn2l. Qed.

Lemma cpable_eexpn2l x m n (x1 : 1 <= x) : cpable (x ^+ m) (x ^+ n).
Proof. by rewrite leq_cpable_wmono //; apply: ler_weexpn2l. Qed.

Lemma ieexprn_weq1 x n (x0 : 0 <= x) (x1 : cpable x 1) :
  (x ^+ n == 1) = ((n == 0%N) || (x == 1)).
Proof.
case: (altP (n =P 0%N))=> [->|n0] /=; first by rewrite eqxx.
case: (cpable_ltrgtP x1)=> hx1; last by rewrite hx1 exp1rn eqxx.
  by apply: ltrWN; rewrite exprn_ilt1.
by apply: ltrNW; rewrite exprn_egt1.
Qed.

Lemma ieexprIn_po x (x0 : 0 < x) (nx1 : x != 1) (x1 : cpable x 1) :
  injective (GRing.exp x).
Proof.
apply: wlog_ltn=> // m n hmn; first by move=> hmn'; rewrite hmn.
move/eqP: hmn; rewrite exprn_addr -{1}[x ^+ m]mulr1 eq_sym (inj_eq (mulfI _)).
  by rewrite ieexprn_weq1 ?ltrW //= (negPf nx1).
by rewrite expf_eq0 ltrNW // andbF.
Qed.

Lemma ler_iexpn2l x (x0 : 0 < x) (x1 : x < 1) :
  {mono (GRing.exp x) : m n / (n <= m)%N >-> m <= n}.
Proof.
apply: (wnmono_leq_mono (wnmono_inj_ltn_lt _ _)); last first.
  by apply: ler_wiexpn2l; rewrite ltrW.
by apply: ieexprIn_po; rewrite ?ltrWN ?ltr_cpable.
Qed.

Lemma ltr_iexpn2l x (x0 : 0 < x) (x1 : x < 1) :
  {mono (GRing.exp x) : m n / (n < m)%N >-> m < n}.
Proof. exact: (leq_lerW_nmono (ler_iexpn2l _ _)). Qed.

Definition lter_iexpn2l := (ler_iexpn2l, ltr_iexpn2l).

Lemma ler_eexpn2l x (x1 : 1 < x) :
  {mono (GRing.exp x) : m n / (m <= n)%N >-> m <= n}.
Proof.
apply: (wmono_leq_mono (wmono_inj_ltn_lt _ _)); last first.
  by apply: ler_weexpn2l; rewrite ltrW.
by apply: ieexprIn_po; rewrite ?ltrNW ?gtr_cpable //; apply: ltr_trans x1.
Qed.

Lemma ltr_eexpn2l x (x1 : 1 < x) :
  {mono (GRing.exp x) : m n / (m < n)%N >-> m < n}.
Proof. exact: (leq_lerW_mono (ler_eexpn2l _)). Qed.

Definition lter_eexpn2l := (ler_eexpn2l, ltr_eexpn2l).

Lemma ltr_expn2r n x y (x0 : 0 <= x) (xy : x < y) : x ^+ n < y ^+ n = (n != 0%N).
Proof.
case: n; [by rewrite ?ltrr | elim=> [|n ihn]; rewrite ?[_ ^+ _.+2]exprS //].
rewrite (@ler_lt_trans _ (x * y ^+ n.+1)) ?lter_wpmul ?ihn //.
  by rewrite ltrW // ihn.
by rewrite exprn_gt0 // (ler_lt_trans x0).
Qed.

Lemma ler_expn2r n : {in >=%R 0 & , {wmono ((@GRing.exp R)^~ n) :/ >=%R}}.
Proof.
move=> x y /= x0 y0 xy; elim: n=> [|n ihn]; rewrite !(expr0, exprS) //.
by rewrite (@ler_trans _ (x * y ^+ n)) ?lter_wpmul ?exprn_ge0.
Qed.

Definition lter_expn2r := (ler_expn2r, ltr_expn2r).

Lemma ltr_wpexpn2r n (hn : (0 < n)%N) :
  {in >=%R 0 & , {wmono ((@GRing.exp R)^~ n) :/ >%R}}.
Proof. by move=> x y /= x0 y0 hxy; rewrite ltr_expn2r // -lt0n. Qed.

End IntegralDomainOperationTheory.
End IntegralDomainTheory.

Module Field.

Include IntegralDomainTheory.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : ring_mixin_of R base }.
Definition base2 R (c : class_of R) := IntegralDomain.Class (mixin c).
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.Field.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := IntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition join_poIdomainType cT :=
  @IntegralDomain.Pack (fieldType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Field.class_of.
Coercion base2 : class_of >-> IntegralDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion poIdomainType : type >-> IntegralDomain.type.
Canonical poIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.

End Exports.

End Field.
Import Field.Exports.

(* Module FieldTheory. *)
(* Section FieldTheory. *)

(* Variable F : Field.type. *)
(* Implicit Types x y z t : F. *)

(* End FieldTheory. *)
(* End FieldTheory. *)

End PartialOrder.

Module TotalOrder.

Import PartialOrder.OrderDef.
Import PartialOrder.IntegralDomain.Exports.

Definition mixin_of (R : PartialOrder.IntegralDomain.type) :=
  forall x : R, (0 <= x) || (0 <= - x).

Section POMixin.

Variable R : GRing.IntegralDomain.type.
Variable le : rel R.
Hypothesis le0_add : forall x y, le 0 x -> le 0 y -> le 0 (x + y).
Hypothesis le0_mul : forall x y, le 0 x -> le 0 y -> le 0 (x * y).
Hypothesis le0_eq0  : forall x,  le 0 x -> le 0 (-x) -> x = 0.
Hypothesis sub_ge0  : forall x y, le x y = le 0 (y - x).
Hypothesis le0_total : forall x, le 0 x || le 0 (- x).

Fact le00 : le 0 0.
Proof. by move: (le0_total 0); rewrite oppr0 orbb. Qed.

Fact le01 : le 0 1.
Proof.
by case/orP: (le0_total 1)=> // ?; rewrite -[1]mul1r -mulrNN le0_mul.
Qed.

Definition PartialMixin := PartialOrder.Mixin le00 le01 le0_add le0_mul le0_eq0 sub_ge0.

End POMixin.

Section POPosMixin.

Variable R : GRing.IntegralDomain.type.
Variable pos : pred R.
Hypothesis pos_add : forall x y, pos x -> pos y -> pos (x + y).
Hypothesis pos_mul : forall x y, pos x -> pos y -> pos (x * y).
Hypothesis pos_eq0  : forall x,  pos x -> pos (-x) -> x = 0.
Hypothesis pos_total : forall x, pos x || pos (- x).

Definition le_pos x y := pos (- x + y).
Fact le_pos0_add x y : le_pos 0 x -> le_pos 0 y -> le_pos 0 (x + y).
Proof. exact: PartialOrder.le_pos0_add. Qed.
Fact le_pos0_mul x y : le_pos 0 x -> le_pos 0 y -> le_pos 0 (x * y).
Proof. exact: PartialOrder.le_pos0_mul. Qed.
Fact le_pos0_eq0 x : le_pos 0 x -> le_pos 0 (-x) -> x = 0.
Proof. exact: PartialOrder.le_pos0_eq0. Qed.
Fact sub_pos_ge0 x y : le_pos x y = le_pos 0 (y - x).
Proof. exact: PartialOrder.sub_pos_ge0. Qed.
Lemma le_pos0_total x : le_pos 0 x || (le_pos 0 (- x)).
Proof. by rewrite /le_pos !oppr0 !add0r. Qed.

Definition PartialPosMixin := PartialMixin le_pos0_add
  le_pos0_mul le_pos0_eq0 sub_pos_ge0 le_pos0_total.

End POPosMixin.


Local Notation oidom_mixin_of T b :=
  (mixin_of (@PartialOrder.IntegralDomain.Pack T b T)).

Section Generic.

(* The BF-prefixed bound variable names are a backward-compatibility patch
   between coq-8.2-1 and coq-trunk r12661 and later
*)

(* Implicits *)
Variables (BFtype base_type : Type) (BFclass_of base_of : Type -> Type).
Variable to_oidom : forall T, base_of T -> PartialOrder.IntegralDomain.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, BFclass_of T -> Type -> BFtype.
Variable Class : forall T b, oidom_mixin_of T (to_oidom b) -> BFclass_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack T b0 (m0 : oidom_mixin_of T b0) :=
  fun bT b & phant_id (base_class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

End Generic.

Implicit Arguments
   gen_pack [BFtype base_type BFclass_of base_of to_oidom base_sort].

Module IntegralDomain.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : PartialOrder.IntegralDomain.class_of R;
  mixin : mixin_of (PartialOrder.IntegralDomain.Pack base R)
}.
Local Coercion base : class_of >-> PartialOrder.IntegralDomain.class_of.
Local Coercion mixin : class_of >-> mixin_of.
Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class PartialOrder.IntegralDomain.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poidomainType cT := PartialOrder.IntegralDomain.Pack (class cT) cT.
Definition join_idomainType cT :=
  @GRing.IntegralDomain.Pack (poidomainType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PartialOrder.IntegralDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion poidomainType : type >-> PartialOrder.IntegralDomain.type.
Canonical poidomainType.
End Exports.

End IntegralDomain.
Import PartialOrder.IntegralDomain.Exports.
Import PartialOrder.Field.Exports.
Import IntegralDomain.Exports.

Module IntegralDomainTheory.

Import PartialOrder.IntegralDomainTheory.

Section IntegralDomainTheory.

Hint Resolve lerr.

Variable R : IntegralDomain.type.
Implicit Types x y z t : R.

Lemma ler0_total x : (0 <= x) || (0 <= - x). Proof. by case: R x=> T []. Qed.

Lemma ler_total : total (@ler R).
Proof.
by move=> x y; rewrite -subr_ge0 -[y <= _]subr_ge0 -oppr_sub orbC ler0_total.
Qed.

Fact cpable_ordered x y : cpable x y. Proof. exact: ler_total. Qed.
Hint Resolve cpable_ordered.

Lemma wlog_ler P : (forall a b, P b a -> P a b)
  -> (forall a b, a <= b -> P a b) -> forall a b : R, P a b.
Proof. by move=> sP hP a b; apply: cpable_wlog_ler (ler_total a b). Qed.

Lemma wlog_ltr P : (forall a, P a a) -> (forall a b, (P b a -> P a b))
  -> (forall a b, a < b -> P a b) -> forall a b : R, P a b.
Proof. by move=> rP sP hP a b; apply: cpable_wlog_ltr (ler_total a b). Qed.

Lemma ltrNge x y : (x < y) = ~~ (y <= x).
Proof. by move=> *; rewrite cpable_ltrNge. Qed.

Lemma lerNgt x y : (x <= y) = ~~ (y < x).
Proof. by move=> *; rewrite cpable_lerNgt. Qed.

Lemma lerP x y : le_xor_gtr x y (x <= y) (y < x).
Proof. exact: cpable_lerP. Qed.

Lemma ltrP x y : ltr_xor_geq x y (y <= x) (x < y).
Proof. exact: cpable_ltrP. Qed.

Lemma ltrgtP x y : cparer x y (y == x) (x == y)
  (x <= y) (y <= x) (x < y) (x > y) .
Proof. exact: cpable_ltrgtP. Qed.

Lemma neqr_lt x y : (x != y) = (x < y) || (y < x).
Proof. exact: cpable_neqr_lt. Qed.

Lemma eqr_leLR x y z t : (x <= y -> z <= t) -> (y < x -> t < z)
  -> (x <= y = (z <= t)).
Proof. by move=> *; apply/idP/idP; rewrite // !lerNgt; apply: contra. Qed.

Lemma eqr_leRL x y z t : (x <= y -> z <= t) -> (y < x -> t < z)
  -> ((z <= t) = (x <= y)).
Proof. by move=> *; symmetry; apply: eqr_leLR. Qed.

Lemma eqr_ltLR x y z t : (x < y -> z < t) -> (y <= x -> t <= z)
  -> (x < y = (z < t)).
Proof. by move=> *; rewrite !ltrNge; congr negb; apply: eqr_leLR. Qed.

Lemma eqr_ltRL x y z t : (x < y -> z < t) -> (y <= x -> t <= z)
  -> ((z < t) = (x < y)).
Proof. by move=> *; symmetry; apply: eqr_ltLR. Qed.

Lemma natr_gt0 n : (0 < n%:R :> R) = (0 < n)%N.
Proof. exact: (ltr_nat _ 0). Qed.

Lemma ler_muln2r n x y : (x *+ n <= y *+ n) = ((n == 0%N) || (x <= y)).
Proof.
apply/idP/idP; last by case/predU1P=> [->|/ler_wmuln2r //]; rewrite !mulr0n.
by apply: contraLR=> /norP [n0]; rewrite -!ltrNge=> /ltr_wmuln2r->.
Qed.

Lemma ltr_muln2r n x y : (x *+ n < y *+ n) = ((n != 0%N) && (x < y)).
Proof. by apply: negb_inj; rewrite negb_and -!lerNgt negbK ler_muln2r. Qed.

Lemma ler_pmuln2r n (hn : (0 < n)%N) : {mono (@GRing.natmul R)^~ n :/ >=%R}.
Proof. by move=> x y /=; rewrite ler_muln2r -leqn0 leqNgt hn. Qed.

Lemma ltr_pmuln2r n (hn : (0 < n)%N) : {mono (@GRing.natmul R)^~ n :/ >%R}.
Proof. exact: lerW_mono (ler_pmuln2r _). Qed.

Section FinGroup.

Import GroupScope.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Proof. by rewrite natr_gt0 cardG_gt0. Qed.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Proof. by rewrite ltrNW // natrG_gt0. Qed.

Lemma natr_indexg_gt0 G H : #|G : H|%:R > 0 :> R.
Proof. by rewrite natr_gt0 indexg_gt0. Qed.

Lemma natr_indexg_neq0 G H : #|G : H|%:R != 0 :> R.
Proof. by rewrite ltrNW // natr_indexg_gt0. Qed.

End FinGroup.

End IntegralDomainTheory.

Hint Resolve cpable_ordered.

Section IntegralDomainMonotonyTheory.

Variables R R' : IntegralDomain.type.
Implicit Types m n p : nat.
Implicit Types x y z : R.
Implicit Types u v w : R'.

Variable D : pred R.
Variable (f : R -> R').

Lemma wmono_mono (mf : {wmono f :/ >%R}) : {mono f :/ >=%R}.
Proof. by move=> x y; rewrite cpable_wmono_ler. Qed.

Lemma wnmono_mono (mf : {wmono f :/~ >%R}) : {mono f :/~ >=%R}.
Proof. by move=> x y; rewrite cpable_wnmono_ler. Qed.

Lemma wmono_mono_in (mf : {in D &, {wmono f :/ >%R}}) : {in D &, {mono f :/ >=%R}}.
Proof. by move=> x y hx hy /=; rewrite (cpable_wmono_in_ler mf). Qed.

Lemma wnmono_mono_in (mf : {in D &, {wmono f :/~ >%R}}) : {in D &, {mono f :/~ >=%R}}.
Proof. by move=> x y hx hy /=; rewrite (cpable_wnmono_in_ler mf). Qed.

End IntegralDomainMonotonyTheory.

Section IntegralDomainOperationTheory.
(* sgr section *)

Hint Resolve lerr.

Variable R : IntegralDomain.type.
Implicit Types x y z t : R.

Lemma sgr_cp0 x :
  ((sgr x == 1) = (0 < x)) *
  ((sgr x == -1) = (x < 0)) *
  ((sgr x == 0) = (x == 0)).
Proof.
rewrite /sgr; case: ltrgtP=> // hx; rewrite ?oner_eq0 ?eqxx;
do !split; rewrite -subr_eq0 ?(subr0, sub0r, oppr_eq0, oner_eq0, opprK) //.
  by rewrite -oppr_add oppr_eq0 -{1}[1]mulr1n -mulrSr pnatr_eq0.
by rewrite -{1}[1]mulr1n -mulrSr pnatr_eq0.
Qed.

Lemma gtr0_sg x : 0 < x -> sgr x = 1.
Proof. by move=> hx; apply/eqP; rewrite sgr_cp0. Qed.

Lemma ltr0_sg x : x < 0 -> sgr x = -1.
Proof. by move=> hx; apply/eqP; rewrite sgr_cp0. Qed.

Lemma sgr0 : sgr (0 : R) = 0. Proof. by rewrite /sgr eqxx. Qed.
Lemma sgr1 : sgr (1 : R) = 1. Proof. by rewrite gtr0_sg // ltr01. Qed.
Lemma sgrN1 : sgr (-1 : R) = -1. Proof. by rewrite ltr0_sg // ltrN10. Qed.

Definition sgrE := (sgr0, sgr1, sgrN1).

CoInductive sgr_val x : bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool -> R -> Set :=
  | SgrNull of x = 0 : sgr_val x true true true true false false
    true false false true false false 0
  | SgrPos of x > 0 : sgr_val x false false true false false true
    false false true false false true 1
  | SgrNeg of x < 0 : sgr_val x false true false false true false
    false true false false true false (-1).

Lemma sgrP x :
  sgr_val x (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
  (0 == sgr x) (-1 == sgr x) (1 == sgr x)
  (sgr x == 0)  (sgr x == -1) (sgr x == 1) (sgr x).
Proof.
by rewrite ![_ == sgr _]eq_sym !sgr_cp0 /sgr lerNgt; case: ltrgtP; constructor.
Qed.

Lemma sgrN x : sgr (-x) = - sgr x.
Proof.
case (ltrgtP x 0)=> hx; last by rewrite hx !(oppr0, sgr0).
  by rewrite gtr0_sg ?oppr_cp0// ltr0_sg// opprK.
by rewrite ltr0_sg ?oppr_cp0// gtr0_sg.
Qed.

Lemma mulr_sg x : sgr x * sgr x = (x != 0)%:R.
Proof. by case: sgrP; rewrite ?(mulr0, mulr1, mulrNN). Qed.

(* Lemma muls_eqA x y z : sgr x != 0 -> *)
(*   (sgr y * sgr z == sgr x) = ((sgr y * sgr x == sgr z) && (sgr z != 0)). *)
(* Proof. by do 3!case: sgrP=> _. Qed. *)

Lemma mulr_sg_eq1 x y : (sgr x * sgr y == 1) = (x != 0) && (sgr x == sgr y).
Proof.
do 2?case: sgrP=> _; rewrite ?(mulr0, mulr1, mulrN1, opprK, oppr0, eqxx);
  by rewrite ?[0 == 1]eq_sym ?oner_eq0 //= eqr_oppC oppr0 oner_eq0.
Qed.

Lemma mulr_sg_eqN1 x y : (sgr x * sgr y == -1) = (x != 0) && (sgr x == - sgr y).
Proof. by rewrite -eqr_oppC -mulrN -sgrN mulr_sg_eq1. Qed.

Lemma sgrM x y : sgr (x * y) = sgr x  * sgr y.
Proof.
case: (sgrP x)=> hx; first by rewrite hx !mul0r sgr0.
  case: (sgrP y)=> hy; first by rewrite hy !mulr0 sgr0.
    by apply/eqP; rewrite mul1r sgr_cp0 mulr_gt0.
  by apply/eqP; rewrite mul1r sgr_cp0 mulr_gt0_lt0.
case: (sgrP y)=> hy; first by rewrite hy !mulr0 sgr0.
  by apply/eqP; rewrite mulr1 sgr_cp0 mulr_lt0_gt0.
by apply/eqP; rewrite mulN1r opprK sgr_cp0 mulr_lt0.
Qed.

Lemma sgrX n x : sgr (x ^+ n) = (sgr x) ^+ n.
Proof. by elim: n => [|n ihn]; rewrite ?sgr1 // !exprS sgrM ihn. Qed.

Lemma sgr_eq0 x : (sgr x == 0) = (x == 0).
Proof. by rewrite sgr_cp0. Qed.

Lemma sgr_odd n x : x != 0 -> (sgr x) ^+ n = (sgr x) ^+ (odd n).
Proof. by case: sgrP=> //=; rewrite ?exp1rn // signr_odd. Qed.

Lemma sgrMn x n : sgr (x *+ n) = (n != 0%N)%:R * sgr x.
Proof.
case: n=> [|n]; first by rewrite mulr0n sgr0 mul0r.
by rewrite mul1r /sgr mulrn_eq0 cpable_mulrn_ge0.
Qed.

(* smul section *)

Lemma sgr_id x : sgr (sgr x) = sgr x.
Proof. by case: (sgrP x) => hx; rewrite sgrE. Qed.

Lemma sgr_smul x y : sgr ((sgr x) * y) = (sgr x) * (sgr y).
Proof. by rewrite sgrM sgr_id. Qed.

Lemma sgr_gt0 x : (sgr x > 0) = (x > 0).
Proof. by rewrite -sgr_cp0 sgr_id sgr_cp0. Qed.

Lemma sgr_lt0 x : (sgr x < 0) = (x < 0).
Proof. by rewrite -sgr_cp0 sgr_id sgr_cp0. Qed.

Lemma sgr_ge0 x : (sgr x >= 0) = (x >= 0).
Proof. by rewrite !lerNgt sgr_lt0. Qed.

Lemma sgr_le0 x : (sgr x <= 0) = (x <= 0).
Proof. by rewrite !lerNgt sgr_gt0. Qed.

(* absr section *)

Lemma absr_dec x : `|x| = sgr x * x.
Proof. by rewrite /absr; case: sgrP; rewrite ?(mul0r, mul1r, mulN1r). Qed.

Lemma absr0 : `|0 : R| = 0 :> R.
Proof. by rewrite /absr lerr. Qed.

Lemma absrN x : `| -x | = `|x|.
Proof. by rewrite !absr_dec sgrN mulrNN. Qed.

Lemma ger0_abs x : (0 <= x) -> `|x| = x.
Proof. by rewrite /absr=> ->. Qed.

Definition gtr0_abs x (hx : 0 < x) := ger0_abs (ltrW hx).

Lemma ler0_abs x : (x <= 0) -> `|x| = -x.
Proof.
move=> hx; rewrite -{1}[x]opprK absrN //.
by apply:ger0_abs; rewrite oppr_cp0.
Qed.

Definition ltr0_abs x (hx : x < 0) := ler0_abs (ltrW hx).

CoInductive absr_val x : R -> bool -> bool -> bool
  -> bool -> bool -> bool -> R -> Set :=
  | AbsNull of x = 0 : absr_val x 0 true true true true false false 0
  | AbsrPos of x > 0 :
    absr_val x x false false false true false true x
  | AbsrNeg of x < 0 :
    absr_val x x false false true false true false (-x).

Lemma absrP x : absr_val x
  x (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (0 < x) `|x|.
Proof.
case: ltrgtP=> hx.
* by rewrite gtr0_abs //; constructor; rewrite // gtr0_abs.
* by rewrite ltr0_abs //; constructor; rewrite // ltr0_abs.
* by rewrite -hx absr0; constructor; rewrite // absr0.
Qed.

CoInductive absrW_val x : R -> bool -> bool -> R -> Set :=
  | AbsrWPos of 0 <= x : absrW_val x x false true x
  | AbsrWNeg of x < 0 : absrW_val x x true false (-x).

Lemma absrWP x : absrW_val x x (x < 0) (0 <= x) `|x|.
Proof. by case: absrP; constructor; rewrite // ?ltrW. Qed.

Lemma absr_idVN x : {`|x| = x} + {`|x| = -x}.
Proof. by rewrite /absr; case: ltrgtP=> _; [right|left|left]. Qed.

Lemma absr_ge0 x : 0 <= `|x|.
Proof. by case: absrP=> //; rewrite ?oppr_cp0; move/ltrW. Qed.
Hint Resolve absr_ge0.

Lemma mulr_sg_abs x : sgr x * `|x| = x.
Proof.
by rewrite absr_dec mulrA mulr_sg; case: ltrgtP; rewrite (mul1r, mul0r).
Qed.

Lemma absr_eq0 x : (`|x| == 0) = (x == 0).
Proof. by rewrite /absr; case: lerP; rewrite ?oppr_eq0. Qed.

Lemma absr_lt0 x : `|x| < 0 = false.
Proof. by apply: negbTE; rewrite -lerNgt. Qed.

Lemma absr_le0 x : (`|x| <= 0) = (x == 0).
Proof.
by case: absrP; rewrite ?lerr ?oppr_cp0 // ?ltrNge; move/negPf.
Qed.

Lemma absr_gt0 x : (`|x| > 0) = (x != 0).
Proof. by rewrite ltrNge absr_le0. Qed.

Lemma absr1 : `|1| = 1 :> R. Proof. by rewrite ger0_abs// ler01. Qed.

Lemma absrN1 : `|-1| = 1 :> R. Proof. by rewrite absrN absr1. Qed.

Lemma absr_id x : `| `|x| | = `|x|. Proof. by rewrite ger0_abs ?absr_ge0. Qed.

Definition absrE x := (absr_id, absr0, absr1, absrN1, absr_ge0, absr_eq0,
  absr_lt0, absr_le0, absr_gt0, absrN).

Lemma distrC x y : `|x - y| = `|y - x|.
Proof. by rewrite -oppr_sub absrN. Qed.

Lemma absrM x y : `|x * y| = `|x| * `|y|.
Proof. by rewrite !absr_dec sgrM -mulrA mulrAC [x * _]mulrC !mulrA. Qed.

Lemma absrX n x : `|x ^+ n| = `|x| ^+ n.
Proof. by elim: n=> [|n ihn]; rewrite ?absr1 // !exprS absrM ihn. Qed.

(* Todo : rename *r_*_le in ler_*_* *)
Lemma ler_abs_add x y : `| x + y | <= `|x| + `|y|.
Proof.
wlog : x y / (x > 0)=> [hxp | xp].
  case: (ltrgtP x 0)=> [xn|xp|->]; last 2 first; do ?exact: hxp.
    by rewrite absr0 !add0r lterr.
  by rewrite -absrN oppr_add (ler_trans (hxp _ _ _)) ?absrN ?oppr_cp0.
case: (ltrgtP y 0)=> hy; last by rewrite hy absr0 !addr0.
  rewrite (@ger0_abs x) ?(ltrW xp) // (@ler0_abs y) ?(ltrW hy) //.
  by case: (lerP 0 (x + y))=> lnyx; [rewrite ger0_abs | rewrite ler0_abs];
    rewrite // ?ltrW // ?oppr_add lter_add2 ?(lt0_cp, gt0_cp).
by rewrite !ger0_abs // ?ltrW // ltr_spsaddr.
Qed.

Lemma ler_abs_sum I r (G : I -> R) (P : pred I):
  `|\sum_(i <- r | P i) G i| <= \sum_(i <- r | P i) `|G i|.
Proof.
apply: (big_ind2 (fun a b => `| a | <= b)); rewrite // ?absr0 //.
by move=> *; rewrite (ler_trans (ler_abs_add _ _)) // ler_add.
Qed.

Lemma ler_dist_add x y : `| x - y | <= `|x| + `|y|.
Proof. by rewrite (ler_trans (ler_abs_add _ _)) ?absrN. Qed.

Lemma ler_sub_absD x y : `|x| - `|y| <= `| x + y |.
Proof.
rewrite -{1}[x](addrK y) lter_sub_addl.
by rewrite (ler_trans (ler_abs_add _ _)) // addrC absrN.
Qed.

Lemma ler_sub_dist x y : `|x| - `|y| <= `| x - y |.
Proof. by rewrite -[`|y|]absrN ler_sub_absD. Qed.

Lemma ler_dist_dist x y : `|`|x| - `|y| | <= `| x - y |.
Proof. by case: absrWP; [|rewrite distrC]; rewrite ?oppr_sub ler_sub_dist. Qed.

Lemma ler_dist_absD x y : `| `|x| - `|y| | <= `| x + y |.
Proof. by rewrite -[y]opprK absrN ler_dist_dist. Qed.

Lemma ler_absl x y : (`|x| <= y) = (-y <= x <= y).
Proof.
case: absrP=> hx; first by rewrite oppr_cp0 andbb.
  case: lerP=> hxy; rewrite andbC //=.
  by symmetry; rewrite ler_oppl (@ler_trans _ x) // ge0_cp // ltrW.
case: (lerP x y)=> hxy; rewrite andbC; first by rewrite ler_oppl.
by apply: negbTE; rewrite -ltrNge (@ler_lt_trans _ x) ?lt0_cp // ltrW.
Qed.

Lemma ler_abslP x y : reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Proof.
by rewrite ler_absl ler_oppl; apply: (iffP (@andP _ _)); case.
Qed.

Implicit Arguments ler_abslP [x y].

Lemma eqr_absl x y : (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof.
apply/idP/idP=> [|/andP [/orP [] /eqP-> /ger0_abs /eqP]]; rewrite ?absrE //.
by move/eqP<-; rewrite absrE andbT; case: absrP; rewrite ?opprK ?eqxx ?orbT.
Qed.

Lemma eqr_abs2 x y : (`|x| == `|y|) = (x == y) || (x == -y).
Proof.
by rewrite eqr_absl absrE andbT; case: absrP=> hy; rewrite ?hy // opprK orbC.
Qed.

Lemma ltr_absl x y : (`|x| < y) = (-y < x < y).
Proof.
rewrite ltr_neqAle ler_absl eqr_absl negb_and negb_or.
case: (lerP 0 y)=> hy; rewrite orbC /=.
  by rewrite !ltr_neqAle [- _ == _]eq_sym; do 2! case: ltrgtP=> ?.
by apply/andP/andP=> [[] /ler_trans|[] /ltr_trans] h /h;
  rewrite (ltrNge, lerNgt) lt0_cp.
Qed.

Definition lter_absl := (ler_absl, ltr_absl).

Lemma ltr_abslP x y : reflect ((-x < y) * (x < y)) (`|x| < y).
Proof. by rewrite ltr_absl ltr_oppl; apply: (iffP (@andP _ _)); case. Qed.

Implicit Arguments ltr_abslP [x y].

Lemma ler_absr x y : (x <= `|y|) = (x <= y) || (x <= -y).
Proof. by rewrite lerNgt ltr_absl negb_and -!lerNgt orbC ler_oppr. Qed.

Lemma ltr_absr x y : (x < `|y|) = (x < y) || (x < -y).
Proof. by rewrite ltrNge ler_absl negb_and -!ltrNge orbC ltr_oppr. Qed.

Definition lter_absr :=  (ler_absr, ltr_absr).

Lemma ler_nabsl x y (hy : y < 0) : (`|x| <= y = false).
Proof. by apply: negbTE; rewrite -ltrNge (ltr_le_trans hy) ?absrE. Qed.

Lemma ltr_nabsl x y (hy : y <= 0) : (`|x| < y = false).
Proof. by apply: negbTE; rewrite -lerNgt (ler_trans hy) ?absrE. Qed.

Definition lter_nabsr := (ler_nabsl, ltr_nabsl).

Lemma ler_distl x y e : (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. by rewrite lter_absl !lter_sub_addl. Qed.

Lemma ltr_distl x y e : (`|x - y| < e) = (y - e < x < y + e).
Proof. by rewrite lter_absl !lter_sub_addl. Qed.

Definition lter_distl := (ler_distl, ltr_distl).

Lemma absr_sg x : `|sgr x| = (x != 0)%:R.
Proof. by case: sgrP; rewrite ?absrE. Qed.

Lemma eqr_abs_id x : (`|x| == x) = (0 <= x).
Proof. by rewrite eqr_absl eqxx. Qed.

Lemma eqr_absN x : (`|x| == -x) = (x <= 0).
Proof. by rewrite eqr_absl opprK eqxx orbT oppr_cp0. Qed.

Definition eqr_abs_idVN := (eqr_abs_id, eqr_absN).

(* ler/ltr and multiplication by a positive/negative *)

Lemma ler_pmul2l x (hx : 0 < x) : {mono *%R x :/ >=%R}.
Proof. exact: wmono_mono (ltr_wpmul2l _). Qed.

Lemma ltr_pmul2l x (hx : 0 < x) : {mono *%R x :/ >%R}.
Proof. exact: lerW_mono (ler_pmul2l _). Qed.

Definition lter_pmul2l := (ler_pmul2l, ltr_pmul2l).

Lemma ler_pmul2r x (hx : 0 < x) : {mono *%R^~ x :/ >=%R}.
Proof. exact: wmono_mono (ltr_wpmul2r _). Qed.

Lemma ltr_pmul2r x (hx : 0 < x) : {mono *%R^~ x :/ >%R}.
Proof. exact: lerW_mono (ler_pmul2r _). Qed.

Definition lter_pmul2r := (ler_pmul2r, ltr_pmul2r).

Lemma ler_nmul2l x (hx : x < 0) : {mono *%R x :/~ >=%R}.
Proof. exact: wnmono_mono (ltr_wnmul2l _). Qed.

Lemma ltr_nmul2l x (hx : x < 0) : {mono *%R x :/~ >%R}.
Proof. exact: lerW_nmono (ler_nmul2l _). Qed.

Definition lter_nmul2l := (ler_nmul2l, ltr_nmul2l).

Lemma ler_nmul2r x (hx : x < 0) : {mono *%R^~ x :/~ >=%R}.
Proof. exact: wnmono_mono (ltr_wnmul2r _). Qed.

Lemma ltr_nmul2r x (hx : x < 0) : {mono *%R^~ x :/~ >%R}.
Proof. exact: lerW_nmono (ler_nmul2r _). Qed.

Definition lter_nmul2r := (ler_nmul2r, ltr_nmul2r).

(* ler/ltr and multiplication between a positive/negative *)
Lemma ler_pmull_l x y : 0 < y -> x * y <= y = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_pmul2r. Qed.

Lemma ltr_pmull_l x y : 0 < y -> x * y < y = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_pmul2r. Qed.

Definition lter_pmull_l := (ler_pmull_l, ltr_pmull_l).

Lemma ler_pmulr_l x y : 0 < y -> y * x <= y = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_pmul2l. Qed.

Lemma ltr_pmulr_l x y : 0 < y -> y * x < y = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_pmul2l. Qed.

Definition lter_pmulr_l := (ler_pmulr_l, ltr_pmulr_l).
Definition lter_pmul_l := (lter_pmull_l, lter_pmulr_l).

Lemma ler_pmull_r x y : 0 < y -> y <= x * y = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_pmul2r. Qed.

Lemma ltr_pmull_r x y : 0 < y -> y < x * y = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_pmul2r. Qed.

Definition lter_pmull_r := (ler_pmull_r, ltr_pmull_r).

Lemma ler_pmulr_r x y : 0 < y -> y <= y * x = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_pmul2l. Qed.

Lemma ltr_pmulr_r x y : 0 < y -> y < y * x = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_pmul2l. Qed.

Definition lter_pmulr_r := (ler_pmulr_r, ltr_pmulr_r).
Definition lter_pmul_r := (ler_pmull_r, ltr_pmulr_r).

Lemma ler_nmull_l x y : y < 0 -> x * y <= y = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_nmul2r. Qed.

Lemma ltr_nmull_l x y : y < 0 -> x * y < y = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_nmul2r. Qed.

Definition lter_nmull_l := (ler_nmull_l, ltr_nmull_l).

Lemma ler_nmulr_l x y : y < 0 -> y * x <= y = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_nmul2l. Qed.

Lemma ltr_nmulr_l x y : y < 0 -> y * x < y = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_nmul2l. Qed.

Definition lter_nmulr_l := (ler_nmulr_l, ltr_nmulr_l).
Definition lter_nmul_l := (lter_nmull_l, lter_nmulr_l).

Lemma ler_nmull_r x y : y < 0 -> y <= x * y = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_nmul2r. Qed.

Lemma ltr_nmull_r x y : y < 0 -> y < x * y = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_nmul2r. Qed.

Definition lter_nmull_r := (ler_nmull_r, ltr_nmull_r).

Lemma ler_nmulr_r x y : y < 0 -> y <= y * x = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_nmul2l. Qed.

Lemma ltr_nmulr_r x y : y < 0 -> y < y * x = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_nmul2l. Qed.

Definition lter_nmulr_r := (ler_nmulr_r, ltr_nmulr_r).
Definition lter_nmul_r := (ler_nmull_r, ltr_nmulr_r).

Lemma exprn_even_ge0 n x : ~~ odd n -> 0 <= x ^+ n.
Proof.
case: n=> [|n]; rewrite ?ler01 //= negbK=> hx.
rewrite ler_eqVlt eq_sym expf_eq0 -sgr_cp0 sgrX /=.
by case x0: (x == 0)=> //=; rewrite sgr_odd ?x0 //= hx expr0.
Qed.

(* Lemma mulN1sr : forall (R' : PartialOrder.IntegralDomain.type) (x : R), *)
(*   sgr (-1 : R') *~ x = -x. *)

Lemma sqr_abs_eq1 x : (x ^+ 2 == 1) = (`|x| == 1).
Proof. by rewrite sqrf_eq1 eqr_absl ler01 andbT. Qed.

Lemma sqrp_eq1 x (hx : 0 <= x) : (x ^+ 2 == 1) = (x == 1).
Proof. by rewrite sqr_abs_eq1 ger0_abs. Qed.

Lemma sqrn_eq1 x (hx : x <= 0) : (x ^+ 2 == 1) = (x == -1).
Proof. by rewrite sqr_abs_eq1 ler0_abs // eqr_oppC. Qed.

(* expr and ler/ltr *)
Lemma exprS_le1 n x (x0 : 0 <= x) : (x ^+ n.+1 <= 1) = (x <= 1).
Proof. by apply: eqr_leRL=> [/exprn_ile1|/exprn_egt1]->. Qed.

Lemma exprS_lt1 n x (x0 : 0 <= x) : (x ^+ n.+1 < 1) = (x < 1).
Proof. by apply: eqr_ltRL=> [/exprn_ilt1|/exprn_ege1]->. Qed.

Definition exprS_lte1 := (exprS_le1, exprS_lt1).

Lemma exprS_ge1 n x (x0 : 0 <= x) : (1 <= x ^+ n.+1) = (1 <= x).
Proof. by rewrite !lerNgt; congr negb; rewrite exprS_lte1. Qed.

Lemma exprS_gt1 n x (x0 : 0 <= x) : (1 < x ^+ n.+1) = (1 < x).
Proof. by rewrite !ltrNge; congr negb; rewrite exprS_lte1. Qed.

Definition exprS_gte1 := (exprS_ge1, exprS_gt1).

Lemma exprS_p_eq1 x n (x0 : 0 <= x) : (x ^+ n.+1 == 1) = (x == 1).
Proof.
case: ltrgtP=> hx; last by rewrite hx exp1rn eqxx.
  by rewrite ltrWN // exprS_lte1.
by rewrite ltrNW // exprS_gte1.
Qed.

Lemma pexprn_eq1 x n (x0 : 0 <= x) : (x ^+ n == 1) = ((n == 0%N) || (x == 1)).
Proof. by rewrite ieexprn_weq1. Qed.

Lemma ieexprIn x (x0 : 0 < x) (nx1 : x != 1) : injective (GRing.exp x).
Proof. exact: ieexprIn_po. Qed.

Lemma ler_pexpn2r n (hn : (0 < n)%N) :
  {in >=%R 0 & , {mono ((@GRing.exp R)^~ n) :/ >=%R}}.
Proof. exact: wmono_mono_in (ltr_wpexpn2r _). Qed.

Lemma ltr_pexpn2r n (hn : (0 < n)%N) :
  {in >=%R 0 & , {mono ((@GRing.exp R)^~ n) :/ >%R}}.
Proof. exact: lerW_mono_in (ler_pexpn2r _). Qed.

Definition lter_pexpn2r := (ler_pexpn2r, ltr_pexpn2r).

Lemma pexpIrn n (hn : (0 < n)%N) : {in (>=%R 0) &, injective ((@GRing.exp R)^~ n)}.
Proof. exact: mono_inj_in (ler_pexpn2r _). Qed.

Lemma eqr_expn2 n x y : (0 < n)%N -> 0 <= x -> 0 <= y ->
  (x ^+ n == y ^+ n) = (x == y).
Proof. by  move=> *; rewrite (inj_in_eq (pexpIrn _)). Qed.

Section MinMax.

Lemma minrC : commutative (@minr R).
Proof. by move=> x y; rewrite /minr; case: ltrgtP. Qed.

Lemma minrr : idempotent (@minr R).
Proof. by move=> x; rewrite /minr lerr. Qed.

Lemma minr_l x y : x <= y -> minr x y = x.
Proof. by rewrite /minr => ->. Qed.

Lemma minr_r x y : y <= x -> minr x y = y.
Proof. by move=> hyx; rewrite minrC minr_l. Qed.

Lemma maxrC : commutative (@maxr R).
Proof. by move=> x y; rewrite /maxr; case: ltrgtP. Qed.

Lemma maxrr : idempotent (@maxr R).
Proof. by move=> x; rewrite /maxr lerr. Qed.

Lemma maxr_l x y : y <= x -> maxr x y = x.
Proof. by move=> hxy; rewrite /maxr hxy. Qed.

Lemma maxr_r x y : x <= y -> maxr x y = y.
Proof. by move=> hxy; rewrite maxrC maxr_l. Qed.

Lemma addr_min_max x y : minr x y + maxr x y = x + y.
Proof.
case: (lerP x y)=> hxy; first by rewrite maxr_r ?minr_l.
by rewrite maxr_l ?minr_r ?ltrW // addrC.
Qed.

Lemma addr_max_min x y : maxr x y + minr x y = x + y.
Proof. by rewrite addrC addr_min_max. Qed.

Lemma minr_to_max x y : minr x y = x + y - maxr x y.
Proof. by rewrite -[x + y]addr_min_max addrK. Qed.

Lemma maxr_to_min x y : maxr x y = x + y - minr x y.
Proof. by rewrite -[x + y]addr_max_min addrK. Qed.

Lemma minrA x y z : minr x (minr y z) = minr (minr x y) z.
Proof.
rewrite /minr; case: (lerP y z)=> hyz; last move/ltrW:hyz=> hyz.
  by case: lerP=> hxy; rewrite ?hyz // (@ler_trans _ y).
case: lerP=> hxz; first by rewrite !(ler_trans hxz).
case: (lerP x y)=> hxy; first by rewrite lerNgt hxz.
by case: ltrgtP hyz.
Qed.

Lemma minrCA : left_commutative (@minr R).
Proof. by move=> x y z; rewrite !minrA [minr x y]minrC. Qed.

Lemma minrAC : right_commutative (@minr R).
Proof. by move=> x y z; rewrite -!minrA [minr y z]minrC. Qed.

CoInductive minr_spec (x y :R) : bool -> bool -> R -> Type :=
| Minr_r of x <= y : minr_spec x y true false x
| Minr_l of y < x : minr_spec x y false true y.

Lemma minrP x y : minr_spec x y (x <= y) (y < x) (minr x y).
Proof.
case: lerP=> hxy; first by rewrite minr_l //; constructor.
by rewrite minr_r 1?ltrW //; constructor.
Qed.

Lemma oppr_max x y : - (maxr x y) = minr (- x) (- y).
Proof.
case: minrP; rewrite lter_opp2 => hxy; first by rewrite maxr_l.
by rewrite maxr_r // ltrW.
Qed.

Lemma oppr_min x y : - (minr x y) = maxr (- x) (- y).
Proof. by rewrite -[maxr _ _]opprK oppr_max !opprK. Qed.

Lemma maxrA x y z : maxr x (maxr y z) = maxr (maxr x y) z.
Proof. by apply/eqP; rewrite -eqr_opp !oppr_max minrA. Qed.

Lemma maxrCA : left_commutative (@maxr R).
Proof. by move=> x y z; rewrite !maxrA [maxr x y]maxrC. Qed.

Lemma maxrAC : right_commutative (@maxr R).
Proof. by move=> x y z; rewrite -!maxrA [maxr y z]maxrC. Qed.

CoInductive maxr_spec (x y :R) : bool -> bool -> R -> Type :=
| Maxr_r of y <= x : maxr_spec x y true false x
| Maxr_l of x < y : maxr_spec x y false true y.

Lemma maxrP x y : maxr_spec x y (y <= x) (x < y) (maxr x y).
Proof.
case: lerP=> hxy; first by rewrite maxr_l //; constructor.
by rewrite maxr_r 1?ltrW //; constructor.
Qed.

Lemma eqr_minl x y : (minr x y == x) = (x <= y).
Proof. by case: minrP=> hxy; rewrite ?eqxx // ltrWN. Qed.

Lemma eqr_minr x y : (minr x y == y) = (y <= x).
Proof. by rewrite minrC eqr_minl. Qed.

Lemma eqr_maxl x y : (maxr x y == x) = (y <= x).
Proof. by case: maxrP=> hxy; rewrite ?eqxx // eq_sym ltrWN. Qed.

Lemma eqr_maxr x y : (maxr x y == y) = (x <= y).
Proof. by rewrite maxrC eqr_maxl. Qed.

Lemma ler_minr x y z : (x <= minr y z) = (x <= y) && (x <= z).
Proof.
case: minrP=> hyz.
  by case: lerP=> hxy //; rewrite (ler_trans _ hyz).
by case: lerP=> hxz; rewrite andbC // (ler_trans hxz) // ltrW.
Qed.

Lemma ler_minl x y z : (minr y z <= x) = (y <= x) || (z <= x).
Proof.
case minrP=> hyz.
  case: lerP=> hyx //=; symmetry; apply: negbTE.
  by rewrite -ltrNge (@ltr_le_trans _ y).
case: lerP=> hzx; rewrite orbC //=; symmetry; apply: negbTE.
by rewrite -ltrNge (@ltr_trans _ z).
Qed.

Lemma ler_maxr x y z : (x <= maxr y z) = (x <= y) || (x <= z).
Proof. by rewrite -lter_opp2 oppr_max ler_minl !ler_opp2. Qed.

Lemma ler_maxl x y z : (maxr y z <= x) = (y <= x) && (z <= x).
Proof. by rewrite -lter_opp2 oppr_max ler_minr !ler_opp2. Qed.

Lemma ltr_minr x y z : (x < minr y z) = (x < y) && (x < z).
Proof. by rewrite !ltrNge ler_minl negb_or. Qed.

Lemma ltr_minl x y z : (minr y z < x) = (y < x) || (z < x).
Proof. by rewrite !ltrNge ler_minr negb_and. Qed.

Lemma ltr_maxr x y z : (x < maxr y z) = (x < y) || (x < z).
Proof. by rewrite !ltrNge ler_maxl negb_and. Qed.

Lemma ltr_maxl x y z : (maxr y z < x) = (y < x) && (z < x).
Proof. by rewrite !ltrNge ler_maxr negb_or. Qed.

Definition lter_minr := (ler_minr, ltr_minr).
Definition lter_minl := (ler_minl, ltr_minl).
Definition lter_maxr := (ler_maxr, ltr_maxr).
Definition lter_maxl := (ler_maxl, ltr_maxl).

Lemma addr_minl : left_distributive +%R (@minr R).
Proof.
move=> x y z; case: minrP=> hxy; first by rewrite minr_l // ler_add2r.
by rewrite minr_r // ltrW // ltr_add2r.
Qed.

Lemma addr_minr : right_distributive +%R (@minr R).
Proof.
move=> x y z; case: minrP=> hxy; first by rewrite minr_l // ler_add2l.
by rewrite minr_r // ltrW // ltr_add2l.
Qed.

Lemma addr_maxl : left_distributive +%R (@maxr R).
Proof.
move=> x y z; rewrite -[_ + _]opprK oppr_add oppr_max.
by rewrite addr_minl -!oppr_add oppr_min !opprK.
Qed.

Lemma addr_maxr : right_distributive +%R (@maxr R).
Proof.
move=> x y z; rewrite -[_ + _]opprK oppr_add oppr_max.
by rewrite addr_minr -!oppr_add oppr_min !opprK.
Qed.

Lemma minrK x y : maxr (minr x y) x = x.
Proof. by case: minrP=> hxy; rewrite ?maxrr ?maxr_r // ltrW. Qed.

Lemma minKr x y : minr y (maxr x y) = y.
Proof. by case: maxrP=> hxy; rewrite ?minrr ?minr_l. Qed.

Lemma maxr_minl : left_distributive (@maxr R) (@minr R).
Proof.
move=> x y z; case: minrP=> hxy.
  by case: maxrP=> hm; rewrite minr_l // ler_maxr (hxy, lerr) ?orbT.
by case: maxrP=> hyz; rewrite minr_r // ler_maxr (ltrW hxy, lerr) ?orbT.
Qed.

Lemma maxr_minr : right_distributive (@maxr R) (@minr R).
Proof. by move=> x y z; rewrite maxrC maxr_minl ![_ _ x]maxrC. Qed.

Lemma minr_maxl : left_distributive (@minr R) (@maxr R).
Proof.
move=> x y z; rewrite -[minr _ _]opprK !oppr_min [- maxr x y]oppr_max.
by rewrite maxr_minl !(oppr_max, oppr_min, opprK).
Qed.

Lemma minr_maxr : right_distributive (@minr R) (@maxr R).
Proof. by move=> x y z; rewrite minrC minr_maxl ![_ _ x]minrC. Qed.


Lemma minr_pmulr (x y z : R) : 0 <= x
  -> x * minr y z = minr (x * y) (x * z).
Proof.
case: sgrP=> // hx _; first by rewrite hx !mul0r minrr.
case: minrP=> hyz; first by rewrite minr_l // ler_pmul2l.
by rewrite minr_r // ltrW // ltr_pmul2l.
Qed.

Lemma minr_nmulr (x y z : R) : x <= 0
  -> x * minr y z = maxr (x * y) (x * z).
Proof.
move=> hx; rewrite -[_ * _]opprK -mulNr minr_pmulr ?oppr_cp0 //.
by rewrite oppr_min !mulNr !opprK.
Qed.

Lemma maxr_pmulr (x y z : R) : 0 <= x
  -> x * maxr y z = maxr (x * y) (x * z).
Proof.
move=> hx; rewrite -[_ * _]opprK -mulrN oppr_max minr_pmulr //.
by rewrite oppr_min !mulrN !opprK.
Qed.

Lemma maxr_nmulr (x y z : R) : x <= 0
  -> x * maxr y z = minr (x * y) (x * z).
Proof.
move=> hx; rewrite -[_ * _]opprK -mulrN oppr_max minr_nmulr //.
by rewrite oppr_max !mulrN !opprK.
Qed.

Lemma minr_pmull (x y z : R) : 0 <= x
  -> minr y z * x = minr (y * x) (z * x).
Proof. by move=> *; rewrite mulrC minr_pmulr // ![_ * x]mulrC. Qed.

Lemma minr_nmull (x y z : R) : x <= 0
  -> minr y z * x = maxr (y * x) (z * x).
Proof. by move=> *; rewrite mulrC minr_nmulr // ![_ * x]mulrC. Qed.

Lemma maxr_pmull (x y z : R) : 0 <= x
  -> maxr y z * x = maxr (y * x) (z * x).
Proof. by move=> *; rewrite mulrC maxr_pmulr // ![_ * x]mulrC. Qed.

Lemma maxr_nmull (x y z : R) : x <= 0
  -> maxr y z * x = minr (y * x) (z * x).
Proof. by move=> *; rewrite mulrC maxr_nmulr // ![_ * x]mulrC. Qed.

Lemma maxrN x : maxr x (- x) = `|x|.
Proof.
case: absrP=> hx; first by rewrite ?hx oppr0 maxrr.
  by rewrite maxr_l // ge0_cp // ltrW.
by rewrite maxr_r // le0_cp // ltrW.
Qed.

Lemma maxNr x : maxr (- x) x = `|x|.
Proof. by rewrite maxrC maxrN. Qed.

Lemma minrN x : minr x (- x) = - `|x|.
Proof. by rewrite -[minr _ _]opprK oppr_min opprK maxNr. Qed.

Lemma minNr x : minr (- x) x = - `|x|.
Proof. by rewrite -[minr _ _]opprK oppr_min opprK maxrN. Qed.

End MinMax.

End IntegralDomainOperationTheory.
End IntegralDomainTheory.

Include IntegralDomainTheory.

Module Field.

Section ClassDef.

Record class_of R :=
  Class { base : PartialOrder.Field.class_of R; mixin : oidom_mixin_of R base }.
Definition base2 R (c : class_of R) := IntegralDomain.Class (@mixin _ c).
Local Coercion base : class_of >-> PartialOrder.Field.class_of.
Local Coercion base2 : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class PartialOrder.Field.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := PartialOrder.IntegralDomain.Pack (class cT) cT.
Definition oIdomainType cT := IntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition poFieldType cT := PartialOrder.Field.Pack (class cT) cT.
Definition join_poIdomainType cT :=
  @PartialOrder.IntegralDomain.Pack (poFieldType cT) (class cT) cT.
Definition join_oIdomainType cT :=
  @IntegralDomain.Pack (poFieldType cT) (class cT) cT.
Definition join_fieldType cT :=
  @GRing.Field.Pack (poFieldType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PartialOrder.Field.class_of.
Coercion base2 : class_of >-> IntegralDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion poIdomainType : type >-> PartialOrder.IntegralDomain.type.
Canonical poIdomainType.
Coercion oIdomainType : type >-> IntegralDomain.type.
Canonical oIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion poFieldType : type >-> PartialOrder.Field.type.
Canonical poFieldType.

Canonical join_poIdomainType.
Canonical join_oIdomainType.
Canonical join_fieldType.

End Exports.

End Field.

Import PartialOrder.IntegralDomain.Exports.
Import PartialOrder.Field.Exports.
Import IntegralDomain.Exports.
Import Field.Exports.

Module FieldTheory.

Import PartialOrder.IntegralDomainTheory.
Import IntegralDomainTheory.

Section FieldTheory.

Variable F : Field.type.
Implicit Types x y z t : F.

Hint Resolve lerr.

Lemma unitf_gt0 x : 0 < x -> GRing.unit x.
Proof. by move=> hx; rewrite unitfE eq_sym ltrWN. Qed.

Lemma unitf_lt0 x : x < 0 -> GRing.unit x.
Proof. by move=> hx; rewrite unitfE ltrWN. Qed.

Lemma invr_ge0 x : (0 <= x^-1) = (0 <= x).
Proof.
case: (ltrgtP x)=> hx; last by rewrite hx invr0 lerr.
  apply/negP; move: hx; rewrite ltr_neqAle -oppr_ge0; case/andP=> nx0 hx hVx.
  by move: (mulr_ge0 hx hVx); rewrite mulNr divff // oppr_cp0 lerNgt ltr01.
move: hx; rewrite lerNgt ltr_neqAle eq_sym; case/andP=> x0 hx.
apply/negP; rewrite -oppr_cp0; move/ltrW=> hVx.
by move: (mulr_ge0 hx hVx); rewrite mulrN divff // oppr_cp0 lerNgt ltr01.
Qed.

Lemma invr_gt0 x : (0 < x^-1) = (0 < x).
Proof. by rewrite !ltr_neqAle invr_ge0 eq_sym invr_eq0 eq_sym. Qed.

Definition invr_gte0 := (invr_ge0, invr_gt0).

Lemma invr_le0 x : (x^-1 <= 0) = (x <= 0).
Proof. by rewrite !lerNgt invr_gte0. Qed.

Lemma invr_lt0 x : (x^-1 < 0) = (x < 0).
Proof. by rewrite !ltrNge invr_gte0. Qed.

Definition invr_lte0 := (invr_le0, invr_lt0).

Lemma invr_sg x : (sgr x)^-1 = sgr x.
Proof. by case: sgrP; rewrite ?(invr0, invrN, invr1). Qed.

Lemma sgrV x : sgr (x^-1) = sgr x.
Proof. by rewrite /sgr invr_eq0 invr_ge0. Qed.

Lemma absrV : {morph (@absr F) : x / x ^-1}.
Proof. by move=> x; rewrite /absr invr_ge0; case: ifP; rewrite ?invrN. Qed.

Lemma ler_pinv : {in >%R 0 &, {mono (@GRing.inv F) :/~ >=%R}}.
Proof.
move=> x y hx hy /=; rewrite -(ler_pmul2l hx) -(ler_pmul2r hy).
by rewrite !(divrr, mulrVK) ?unitf_gt0 // mul1r.
Qed.

Lemma ler_ninv : {in <%R 0 &, {mono (@GRing.inv F) :/~ >=%R}}.
Proof.
move=> x y hx hy /=; rewrite -(ler_nmul2l hx) -(ler_nmul2r hy).
by rewrite !(divrr, mulrVK) ?unitf_lt0 // mul1r.
Qed.

Lemma ltr_pinv : {in >%R 0 &, {mono (@GRing.inv F) :/~ >%R}}.
Proof. exact: lerW_nmono_in ler_pinv. Qed.

Lemma ltr_ninv: {in <%R 0 &, {mono (@GRing.inv F) :/~ >%R}}.
Proof. exact: lerW_nmono_in ler_ninv. Qed.

Definition lter_pinv := (ler_pinv, ltr_pinv).
Definition lter_ninv := (ler_ninv, ltr_ninv).

Lemma invr_gt1 x (hx : 0 < x) : (1 < x^-1) = (x < 1).
Proof. by rewrite -{1}[1]invr1 ltr_pinv -?topredE /= ?ltr01. Qed.

Lemma invr_ge1 x (hx : 0 < x) : (1 <= x^-1) = (x <= 1).
Proof. by rewrite -{1}[1]invr1 ler_pinv -?topredE /= ?ltr01. Qed.

Definition invr_gte1 := (invr_ge1, invr_gt1).

Lemma invr_le1 x (hx : 0 < x) : (x^-1 <= 1) = (1 <= x).
Proof. by rewrite -invr_ge1 ?invr_gt0 // invrK. Qed.

Lemma invr_lt1 x (hx : 0 < x) : (x^-1 < 1) = (1 < x).
Proof. by rewrite -invr_gt1 ?invr_gt0 // invrK. Qed.

Definition invr_lte1 := (invr_le1, invr_lt1).
Definition invr_cp1 := (invr_gte1, invr_lte1).

(* all those lemma are a combination of mono(LR|RL) with [pn]mulr_mono[rl] *)
Lemma ler_pdivl_mulr z x y (hz : 0 < z) : (x <= y / z) = (x * z <= y).
Proof. by move=> *; rewrite -(@ler_pmul2r _ z) ?mulrVK ?unitf_gt0. Qed.

Lemma ltr_pdivl_mulr z x y : 0 < z -> (x < y / z) = (x * z < y).
Proof. by move=> *; rewrite -(@ltr_pmul2r _ z) ?mulrVK ?unitf_gt0. Qed.

Definition lter_pdivl_mulr := (ler_pdivl_mulr, ltr_pdivl_mulr).

Lemma ler_pdivr_mulr z x y : 0 < z -> (y / z <= x) = (y <= x * z).
Proof. by move=> *; rewrite -(@ler_pmul2r _ z) ?mulrVK ?unitf_gt0. Qed.

Lemma ltr_pdivr_mulr z x y : 0 < z -> (y / z < x) = (y < x * z).
Proof. by move=> *; rewrite -(@ltr_pmul2r _ z) ?mulrVK ?unitf_gt0. Qed.

Definition lter_pdivr_mulr := (ler_pdivr_mulr, ltr_pdivr_mulr).

Lemma ler_pdivl_mull z x y : 0 < z -> (x <= z^-1 * y) = (z * x <= y).
Proof. by move=> *; rewrite mulrC ler_pdivl_mulr ?[z * _]mulrC. Qed.

Lemma ltr_pdivl_mull z x y : 0 < z -> (x < z^-1 * y) = (z * x < y).
Proof. by move=> *; rewrite mulrC ltr_pdivl_mulr ?[z * _]mulrC. Qed.

Definition lter_pdivl_mull := (ler_pdivl_mull, ltr_pdivl_mull).

Lemma ler_pdivr_mull z x y : 0 < z -> (z^-1 * y <= x) = (y <= z * x).
Proof. by move=> *; rewrite mulrC ler_pdivr_mulr ?[z * _]mulrC. Qed.

Lemma ltr_pdivr_mull z x y : 0 < z -> (z^-1 * y < x) = (y < z * x).
Proof. by move=> *; rewrite mulrC ltr_pdivr_mulr ?[z * _]mulrC. Qed.

Definition lter_pdivr_mull := (ler_pdivr_mull, ltr_pdivr_mull).

Lemma ler_ndivl_mulr z x y : z < 0 -> (x <= y / z) = (y <= x * z).
Proof. by move=> *; rewrite -(@ler_nmul2r _ z) ?mulrVK  ?unitf_lt0. Qed.

Lemma ltr_ndivl_mulr z x y : z < 0 -> (x < y / z) = (y < x * z).
Proof. by move=> *; rewrite -(@ltr_nmul2r _ z) ?mulrVK ?unitf_lt0. Qed.

Definition lter_ndivl_mulr := (ler_ndivl_mulr, ltr_ndivl_mulr).

Lemma ler_ndivr_mulr z x y : z < 0 -> (y / z <= x) = (x * z <= y).
Proof. by move=> *; rewrite -(@ler_nmul2r _ z) ?mulrVK ?unitf_lt0. Qed.

Lemma ltr_ndivr_mulr z x y : z < 0 -> (y / z < x) = (x * z < y).
Proof. by move=> *; rewrite -(@ltr_nmul2r _ z) ?mulrVK ?unitf_lt0. Qed.

Definition lter_ndivr_mulr := (ler_ndivr_mulr, ltr_ndivr_mulr).

Lemma ler_ndivl_mull z x y : z < 0 -> (x <= z^-1 * y) = (y <= z * x).
Proof. by move=> *; rewrite mulrC ler_ndivl_mulr ?[z * _]mulrC. Qed.

Lemma ltr_ndivl_mull z x y : z < 0 -> (x < z^-1 * y) = (y < z * x).
Proof. by move=> *; rewrite mulrC ltr_ndivl_mulr ?[z * _]mulrC. Qed.

Definition lter_ndivl_mull := (ler_ndivl_mull, ltr_ndivl_mull).

Lemma ler_ndivr_mull z x y : z < 0 -> (z^-1 * y <= x) = (z * x <= y).
Proof. by move=> *; rewrite mulrC ler_ndivr_mulr ?[z * _]mulrC. Qed.

Lemma ltr_ndivr_mull z x y : z < 0 -> (z^-1 * y < x) = (z * x < y).
Proof. by move=> *; rewrite mulrC ltr_ndivr_mulr ?[z * _]mulrC. Qed.

Definition lter_ndivr_mull := (ler_ndivr_mull, ltr_ndivr_mull).

Local Notation mid x y := ((x + y) / 2%:R).

Lemma midf_le x y (lxy : x <= y) : (x <= mid x y) * (mid x y  <= y).
Proof.
rewrite ler_pdivl_mulr ?ler_pdivr_mulr ?ltr0Sn //.
by rewrite !mulr_addr !mulr1 ler_add2r ler_add2l.
Qed.

Lemma midf_lt x y (lxy : x < y) : (x < mid x y) * (mid x y  < y).
Proof.
rewrite ltr_pdivl_mulr ?ltr_pdivr_mulr ?ltr0Sn //.
by rewrite !mulr_addr !mulr1 ltr_add2r ltr_add2l.
Qed.

Definition midf_lte := (midf_le, midf_lt).

Lemma natf_div (m d : nat) : (d %| m)%N -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof. by apply: char0_natf_div; apply: (@char_po F). Qed.

Section FinGroup.

Import GroupScope.

Variable gT : finGroupType.

Lemma natf_indexg (G H : {group gT}) :
  H \subset G -> #|G : H|%:R = (#|G|%:R / #|H|%:R)%R :> F.
Proof. by move=> sHG; rewrite -divgS // natf_div ?cardSg. Qed.

End FinGroup.

End FieldTheory.
End FieldTheory.
Include FieldTheory.

Module RealClosedField.

Section ClassDef.

Definition axiom (F : Field.type) := forall (p : {poly F}) (a b : F), a <= b
    -> p.[a] <= 0 <= p.[b] -> { x | a <= x <= b & root p x }.

Record mixin_of (F : Field.type) := Mixin {
  _ : axiom F
}.

Record class_of (R : Type) : Type := Class {
  base : Field.class_of R;
  mixin : mixin_of (Field.Pack base R)
}.
Local Coercion base : class_of >-> Field.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack T b0 (m0 : mixin_of (@Field.Pack T b0 T)) :=
  fun bT b & phant_id (Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := PartialOrder.IntegralDomain.Pack (class cT) cT.
Definition oIdomainType cT := IntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition poFieldType cT := PartialOrder.Field.Pack (class cT) cT.
Definition oFieldType cT := Field.Pack (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Field.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion poIdomainType : type >-> PartialOrder.IntegralDomain.type.
Canonical poIdomainType.
Coercion oIdomainType : type >-> IntegralDomain.type.
Canonical oIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion poFieldType : type >-> PartialOrder.Field.type.
Canonical poFieldType.
Coercion oFieldType : type >-> Field.type.
Canonical oFieldType.
End Exports.

End RealClosedField.
Import RealClosedField.Exports.

Module RealClosedFieldTheory.

Lemma poly_ivt (R : RealClosedField.type) : RealClosedField.axiom R.
Proof. by move: R=> [? [? []]]. Qed.

End RealClosedFieldTheory.
Include RealClosedFieldTheory.

End TotalOrder.

Module Theory.
Export PartialOrder.IntegralDomainTheory.
(* Export PartialOrder.FieldTheory. *)
Export TotalOrder.IntegralDomainTheory.
Export TotalOrder.FieldTheory.
Export TotalOrder.RealClosedFieldTheory.

Hint Resolve @ler01.
Hint Resolve @ltr01.
Hint Resolve lerr.
Hint Resolve ler_trans.
Hint Resolve ltr_trans.
Hint Resolve absr_ge0.
Hint Resolve ler_total.
Hint Resolve cpable_ordered.

End Theory.

End OrderedRing.

Export OrderedRing.PartialOrder.IntegralDomain.Exports.
Export OrderedRing.PartialOrder.Field.Exports.
Export OrderedRing.TotalOrder.IntegralDomain.Exports.
Export OrderedRing.TotalOrder.Field.Exports.
Export OrderedRing.TotalOrder.RealClosedField.Exports.

Notation PartialOrderMixin := OrderedRing.PartialOrder.Mixin.
Notation TotalOrder_PartialMixin := OrderedRing.TotalOrder.PartialMixin.
Notation PartialOrderPosMixin := OrderedRing.PartialOrder.PosMixin.
Notation TotalOrder_PartialPosMixin := OrderedRing.TotalOrder.PartialPosMixin.
Notation TotalOrderPosMixin := OrderedRing.TotalOrder.le_pos0_total.

Notation poIdomainType := OrderedRing.PartialOrder.IntegralDomain.type.
Notation poFieldType := OrderedRing.PartialOrder.Field.type.
Notation oIdomainType := OrderedRing.TotalOrder.IntegralDomain.type.
Notation oFieldType := OrderedRing.TotalOrder.Field.type.
Notation rcfType := OrderedRing.TotalOrder.RealClosedField.type.

Notation POIdomainType T m :=
  (@OrderedRing.PartialOrder.IntegralDomain.pack T _ m _ _ id _ id).
Notation POFieldType T m :=
  (@OrderedRing.PartialOrder.Field.pack T _ m _ _ id _ id).
Notation OIdomainType T m :=
  (@OrderedRing.TotalOrder.IntegralDomain.pack T _ m _ _ id _ id).
Notation OFieldType T m :=
  (@OrderedRing.TotalOrder.Field.pack T _ m _ _ id _ id).
Notation RcfType T m :=
  (@OrderedRing.TotalOrder.RealClosedField.pack T _ m _ _ id _ id).

Notation "[ 'poIdomainType' 'of' T ]" :=
    (@OrderedRing.PartialOrder.IntegralDomain.clone T _ _ id)
  (at level 0, format "[ 'poIdomainType'  'of'  T ]") : form_scope.
Notation "[ 'poFieldType' 'of' T ]" :=
  (@OrderedRing.PartialOrder.Field.clone T _ _ id)
  (at level 0, format "[ 'poFieldType'  'of'  T ]") : form_scope.
Notation "[ 'oIdomainType' 'of' T ]" :=
    (@OrderedRing.TotalOrder.IntegralDomain.clone T _ _ id)
  (at level 0, format "[ 'oIdomainType'  'of'  T ]") : form_scope.
Notation "[ 'oFieldType' 'of' T ]" :=
  (@OrderedRing.TotalOrder.Field.clone T _ _ id)
  (at level 0, format "[ 'oFieldType'  'of'  T ]") : form_scope.
Notation "[ 'rcfType' 'of' T ]" :=
  (@OrderedRing.TotalOrder.RealClosedField.clone T _ _ id)
  (at level 0, format "[ 'rcfType'  'of'  T ]") : form_scope.

Notation rcf_axiom := (@OrderedRing.TotalOrder.RealClosedField.axiom).

Notation ">=%R" := (@OrderedRing.PartialOrder.OrderDef.ler _) : ring_scope.
Notation "x <= y" := (OrderedRing.PartialOrder.OrderDef.ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T))
  (at level 70, y at next level) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T))
  (at level 70, y at next level, only parsing) : ring_scope.
Notation "<=%R" := [rel x y | y <= x] : ring_scope.


Notation ">%R" := (@OrderedRing.PartialOrder.OrderDef.ltr _) : ring_scope.
Notation "x < y"  := (OrderedRing.PartialOrder.OrderDef.ltr x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T))
  (at level 70, y at next level) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T))
  (at level 70, y at next level, only parsing) : ring_scope.
Notation "<%R" := [rel x y | y < x] : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.
Notation "`| x |" := (OrderedRing.PartialOrder.OrderDef.absr x) : ring_scope.
Notation sgr := (@OrderedRing.PartialOrder.OrderDef.sgr _).
Notation maxr := (@OrderedRing.PartialOrder.OrderDef.maxr _).
Notation minr := (@OrderedRing.PartialOrder.OrderDef.minr _).
Notation mid x y := ((x + y) / 2%:R).
Notation cpable := (@OrderedRing.PartialOrder.OrderDef.cpable _).