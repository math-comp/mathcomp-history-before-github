(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
Require Import bigop ssralg finset fingroup zmodp.
Require Import poly.

(*****************************************************************************)
(*          x <= y == x is smaller than y                                    *)
(*           x < y := (x <= y) && (x != y)                                   *)
(*           sgr x == sign of x, equals (0 : R) if and only x == 0,          *)
(*      ORing.sg x == sign of x, equals (0 : R) if and only x == 0,          *)
(*                    equals (1 : R) if x is positive, and -1 otherwise      *)
(*            `|x| == x if x is positive and - x otherwise                   *)
(*   ORing.min x y == minimum of x y                                         *)
(*   ORing.max x y == maximum of x y                                         *)
(*                                                                           *)
(* - list of prefixes :                                                      *)
(*   p : positive                                                            *)
(*   n : negative                                                            *)
(*   sp : strictly positive                                                  *)
(*   sn : strictly negative                                                  *)
(*   i : interior = in [0, 1] or ]0, 1[                                      *)
(*   e : exterior = in [1, +oo[ or ]1; +oo[                                  *)
(*   w : non strict (weak) monotony                                          *)
(*                                                                           *)
(* More documentation soon                                                   *)
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

Reserved Notation "x <= y ?= 'iff' c" (at level 70, y at next level,
  format "x '[hv'  <=  y '/'  ?=  'iff'  c ']'").
Reserved Notation "x <= y ?= 'iff' c :> T" (at level 70, y at next level,
  c at next level, format "x '[hv'  <=  y '/'  ?=  'iff'  c  :> T ']'").

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

Section MoreSsralg.

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

(* :TODO: + version in idomainType *)
Lemma addf_div2 (R : fieldType) (a b c d : R) : b != 0 -> d != 0 ->
  a / b + c / d = (a * d + c * b) / (b * d).
Proof.
move=> b_neq0 d_neq0; apply: (@mulIf _ (b * d)); rewrite ?divfK ?mulf_neq0 //.
by rewrite mulrDl mulrA divfK // [b * d]mulrC mulrA divfK.
Qed.

Lemma mulrMM (R : comRingType) (a b c d : R) :
  (a * b) * (c * d) = (a * c) * (b * d).
Proof. by rewrite !mulrA [a * _ * _]mulrAC. Qed.

(* :TODO: + version in idomainType *)
Lemma mulf_div2 (R : fieldType) (a b c d : R) :
  (a / b) * (c / d) = (a * c) / (b * d).
Proof. by rewrite mulrMM -invfM. Qed.

Lemma signrN (R : unitRingType) b : (-1) ^+ (~~ b) = - (-1) ^+ b :> R.
Proof. by case: b; rewrite // opprK. Qed.

Lemma mulrM_sign (R : idomainType) (s1 s2 : bool) (a b : R) :
  ((-1) ^+ s1 * a) * ((-1) ^+ s2 * b) = (-1) ^+ (s1 (+) s2) * (a * b).
Proof. by rewrite mulrMM -signr_addb. Qed.

Lemma invr_sign (R : unitRingType) (s : bool) : ((-1) ^- s) = (-1) ^+ s :> R.
Proof. by case: s; rewrite ?(invr0, invrN) invr1. Qed.

(* :TODO: + version in idomainType *)
Lemma dvdfM_sign (R : fieldType) (s1 s2 : bool) (a b : R) :
  ((-1) ^+ s1 * a) / ((-1) ^+ s2 * b) = (-1) ^+ (s1 (+) s2) * (a / b).
Proof. by rewrite invfM invr_sign mulrM_sign. Qed.

Lemma sqr_eq0 (R : idomainType) (x : R) : (x ^+ 2 == 0) = (x == 0).
Proof. by rewrite expf_eq0. Qed.

End MoreSsralg.

Module ORing.

Record mixin_of (R : ringType) := Mixin {
  le_op : rel R;
  lt_op : rel R;
  norm_op : R -> R;
  _ : forall x y, le_op (norm_op (x + y)) (norm_op x + norm_op y);
  _ : forall x y, lt_op 0 x -> lt_op 0 y -> lt_op 0 (x + y);
  _ : forall x, norm_op x = 0 -> x = 0;
  _ : forall x y, le_op 0 x -> le_op 0 y -> le_op x y || le_op y x;
  _ : {morph norm_op : x y / x * y};
  _ : forall x y, (le_op x y) = (norm_op (y - x) == y - x);
  _ : forall x y, (lt_op x y) = (y != x) && (le_op x y)
}.

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

Module PIntegralDomain.

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

End PIntegralDomain.
Import PIntegralDomain.Exports.

Open Scope ring_scope.

Module OrderDef.

Definition ltr (R : PIntegralDomain.type) : rel R := lt_op (PIntegralDomain.class R).
Notation ">%R" := (@ltr _) : ring_scope.
Notation "x < y"  := (ltr x y) : ring_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) : ring_scope.
Notation "x > y"  := (y < x) (only parsing) : ring_scope.
Notation "x > y :> T" := ((x : T) > (y : T)) (only parsing) : ring_scope.
Notation "<%R" := [rel x y | y < x] : ring_scope.

Definition ler (R : PIntegralDomain.type) : rel R := le_op (PIntegralDomain.class R).
Notation ">=%R" := (@ler _) : ring_scope.
Notation "x <= y" := (ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T)) (only parsing) : ring_scope.
Notation "<=%R" := [rel x y | y <= x] : ring_scope.

Notation "x <= y <= z" := ((x <= y) && (y <= z)) : ring_scope.
Notation "x < y <= z" := ((x < y) && (y <= z)) : ring_scope.
Notation "x <= y < z" := ((x <= y) && (y < z)) : ring_scope.
Notation "x < y < z" := ((x < y) && (y < z)) : ring_scope.

Definition normr (R : PIntegralDomain.type) : R -> R :=
  norm_op (PIntegralDomain.class R).
Notation "`| x |" := (@normr _ x) : ring_scope.
Prenex Implicits normr.

Definition sgr (R : PIntegralDomain.type) (x : R) : R :=
  if x == 0 then 0 else if (x < 0) then -1 else 1.

Definition minr (R : PIntegralDomain.type) (x y : R) :=
  if x <= y then x else y.
Definition maxr (R : PIntegralDomain.type) (x y : R) :=
  if y <= x then x else y.

Definition Rreal (R : PIntegralDomain.type) : pred R :=
  (fun x => (0 <= x) || (x <= 0)).

Prenex Implicits sgr minr maxr normr Rreal.

Definition lerif (R : PIntegralDomain.type) (x y : R) c :=
  ((x <= y) * ((x == y) = c))%type.
Notation "<?=%R" := lerif : ring_scope.
Notation "x <= y ?= 'iff' c" := (lerif x y c) : ring_scope.
Notation "x <= y ?= 'iff' c :> R" := ((x : R) <= (y : R) ?= iff c) : ring_scope.

Coercion ler_of_leif (R : PIntegralDomain.type)
  (x y : R) c (le_xy : x <= y ?= iff c) := le_xy.1 : x <= y.

End OrderDef.
Import OrderDef.

Notation norm := (@ORing.OrderDef.normr _).
Notation sg := (@ORing.OrderDef.sgr _).
Notation max := (@ORing.OrderDef.maxr _).
Notation min := (@ORing.OrderDef.minr _).
Notation real := (@ORing.OrderDef.Rreal _).

Prenex Implicits Rreal.

Module PIntegralDomainTheory.

Section PIntegralDomainTheory.

Variable R : PIntegralDomain.type.
Implicit Types x y z t : R.

(* Lemmas from the signature *)

Lemma normr0_eq0 x : `|x| = 0 -> x = 0.
Proof. by case: R x => ? [? []]. Qed.

Lemma ler_norm_add x y : `|x + y| <= `|x| + `|y|.
Proof. by case: R x y => ? [? []]. Qed.

Lemma addr_gt0 x y : 0 < x -> 0 < y -> 0 < x + y.
Proof. by case: R x y => ? [? []]. Qed.

Lemma ger_leVge x y : 0 <= x -> 0 <= y -> (x <= y) || (y <= x).
Proof. by case: R x y => ? [? []]. Qed.

Lemma normrM : {morph normr : x y / x * y : R}.
Proof. by case: R => ? [? []]. Qed.

Lemma ler_def x y : (x <= y) = (`|y - x| == y - x).
Proof. by case: R x y => ? [? []]. Qed.

Lemma ltr_def x y : (x < y) = (y != x) && (x <= y).
Proof. by case: R x y => ? [? []]. Qed.

(* General properties of normr, <= and < *)

Lemma ger0_def x : (0 <= x) = (`|x| == x).
Proof. by rewrite ler_def subr0. Qed.

Lemma normr_idP {x} : reflect (`|x| = x) (0 <= x).
Proof. by rewrite ger0_def; apply: eqP. Qed.

Lemma ger0_norm x : 0 <= x -> `|x| = x. Proof. exact: normr_idP. Qed.

Lemma normr1 : `|1| = 1 :> R.
Proof.
apply: (@mulfI _ `|1|); last by rewrite -normrM !mulr1.
by apply/negP=> /eqP /normr0_eq0 /eqP; rewrite oner_eq0.
Qed.

Lemma ler01 : 0 <= 1 :> R. Proof. by rewrite ger0_def normr1. Qed.
Hint Resolve ler01.

Lemma ltr01 : 0 < 1 :> R. Proof. by rewrite ltr_def oner_eq0 ler01. Qed.
Hint Resolve ltr01.

Lemma ltr0Sn n : 0 < n.+1%:R :> R.
Proof. by elim: n=> // n; apply: addr_gt0. Qed.
Hint Resolve ltr0Sn.

Lemma ltr0n n : (0 < n%:R :> R) = (0 < n)%N.
Proof. by case: n; last exact: ltr0Sn; rewrite ltr_def eqxx. Qed.

Lemma ltrW x y : x < y -> x <= y. Proof. by rewrite ltr_def => /andP []. Qed.
Hint Resolve ltrW.

Lemma normr0 : `|0| = 0 :> R.
Proof.
apply: (addrI `|0|); rewrite addr0 -mulr2n -mulr_natl.
by rewrite -(normr_idP (ltrW (ltr0Sn _))) -normrM mulr0.
Qed.

Lemma lerr x : x <= x. Proof. by rewrite ler_def subrr normr0. Qed.
Hint Resolve lerr.

Lemma ltr_neqAle x y : (x < y) = (x != y) && (x <= y).
Proof. by rewrite ltr_def eq_sym. Qed.

Lemma ltrr x : x < x = false. Proof. by rewrite ltr_neqAle eqxx. Qed.

Lemma ler_eqVlt x y : (x <= y) = (x == y) || (x < y).
Proof.
by rewrite ltr_neqAle; have [->|] // := altP (_ =P _); rewrite lerr.
Qed.

Lemma lt0r x : (0 < x) = (x != 0) && (0 <= x). Proof. by rewrite ltr_def. Qed.

Lemma le0r x : (0 <= x) = (x == 0) || (0 < x).
Proof. by rewrite ler_eqVlt eq_sym. Qed.

Lemma ler0n n : 0 <= n%:R :> R. Proof. by case: n=> // n; rewrite ltrW. Qed.
Hint Resolve ler0n.

Lemma normr_nat n : `|n%:R| = n%:R :> R. Proof. by rewrite (normr_idP _). Qed.

Lemma normrMn x n : `|x *+ n| = `|x| *+ n.
Proof. by rewrite -mulr_natl normrM normr_nat mulr_natl. Qed.

Lemma gtr_eqF x y : y < x -> x == y = false.
Proof. by rewrite ltr_def; case/andP; move/negPf=> ->. Qed.

Lemma ltr_eqF x y : x < y -> x == y = false.
Proof. by move=> hyx; rewrite eq_sym gtr_eqF. Qed.

Lemma pnatr_eq0 n : (n%:R == 0 :> R) = (n == 0)%N.
Proof. by case: n=> [|n]; rewrite ?mulr0n ?eqxx // gtr_eqF. Qed.

Lemma normr0P {x} : reflect (`|x| = 0) (x == 0).
Proof. by apply: (iffP eqP)=> [->|/normr0_eq0 //]; apply: normr0. Qed.

Definition normr_eq0 x := sameP (`|x| =P 0) normr0P.

Lemma normrN1 : normr (- 1) = 1 :> R.
Proof.
have /eqP := normrM (- 1) (- 1); rewrite mulrN1 opprK normr1 eq_sym.
rewrite sqrf_eq1; case/orP=> [/eqP //|].
rewrite -ger0_def ler_eqVlt eq_sym oppr_eq0 oner_eq0 => /= /(addr_gt0 ltr01).
by rewrite subrr ltrr.
Qed.

Lemma normrN x : `|- x| = `|x|.
Proof. by rewrite -mulN1r normrM normrN1 mul1r. Qed.

Lemma distrC x y : `|x - y| = `|y - x|.
Proof. by rewrite -opprB normrN. Qed.

Lemma normr_id x : `|`|x| | = `|x|.
Proof.
have norm2r y : `|2%:R * `|y| | = 2%:R * `|y|.
  have := ler_norm_add y (- y).
  by rewrite subrr normr0 normrN -mulr2n mulr_natl=> /normr_idP.
apply: (@mulfI _ `|2%:R|); first by rewrite normr_nat ?pnatr_eq0.
by rewrite -normrM norm2r; congr (_ * _); rewrite -mulr_natl -{2 4}normr1.
Qed.

Lemma normr_ge0 x : 0 <= `|x|. Proof. by apply/normr_idP; apply: normr_id. Qed.
Hint Resolve normr_ge0.

Lemma ler_asym : antisymmetric (>=%R : rel R).
Proof.
move=> x y; rewrite !ler_def distrC => /andP [/eqP->]; apply: contraTeq=> neq_xy.
by rewrite eq_sym -subr_eq0 opprB -mulr2n -mulr_natl mulf_neq0 ?pnatr_eq0 ?subr_eq0.
Qed.

Lemma eqr_le x y : (x == y) = (x <= y <= x).
Proof. by apply/eqP/idP=> [->|/ler_asym]; rewrite ?lerr. Qed.

Lemma subr_ge0 x y : (0 <= y - x) = (x <= y).
Proof. by rewrite ger0_def ler_def. Qed.

Lemma subr_gt0 x y : (0 < y - x) = (x < y).
Proof. by rewrite !ltr_def subr_eq0 subr_ge0. Qed.

Lemma ltr_trans : transitive (@ltr R).
Proof.
move=> y x z le_xy le_yz.
by rewrite -subr_gt0 -(subrK y z) -addrA addr_gt0 ?subr_gt0.
Qed.

Lemma pmulr_rge0 x y : 0 < x -> (0 <= x * y) = (0 <= y).
Proof.
rewrite lt0r !ger0_def normrM => /andP [x_neq0 /eqP ->].
by rewrite (inj_eq (mulfI x_neq0)).
Qed.

Lemma ler_lt_trans y x z : x <= y -> y < z -> x < z.
Proof. by rewrite !ler_eqVlt => /orP[/eqP -> //|/ltr_trans]; apply. Qed.

Lemma ltr_le_trans y x z : x < y -> y <= z -> x < z.
Proof. by rewrite !ler_eqVlt => lxy /orP[/eqP <- //|/(ltr_trans lxy)]. Qed.

Lemma ler_trans : transitive (@ler R).
Proof.
move=> y x z; rewrite !ler_eqVlt => /orP [/eqP -> //|lxy].
by move=> /orP [/eqP <-|/(ltr_trans lxy) ->]; rewrite ?lxy orbT.
Qed.

Lemma pmulr_rgt0 x y : 0 < x -> (0 < x * y) = (0 < y).
Proof.
by move=> x_gt0; rewrite !lt0r mulf_eq0 pmulr_rge0 // negb_or (gtr_eqF x_gt0).
Qed.

Definition lter01 := (ler01, ltr01).

Definition lterr := (lerr, ltrr).

Lemma addr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= (x + y).
Proof.
by rewrite !le0r => /orP [/eqP->|x0] /orP [/eqP->|y0];
  rewrite ?addr0 ?add0r ?eqxx ?x0 ?y0 ?addr_gt0 ?orbT.
Qed.

Lemma lerifP x y c :
   reflect (x <= y ?= iff c) (if c then x == y else x < y).
Proof.
rewrite /lerif ler_eqVlt; apply: (iffP idP)=> [|[]].
  by case: c=> [/eqP->|lxy]; rewrite ?eqxx // lxy ltr_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // ltr_eqF.
Qed.

(* Comparision to 0 of a difference *)

(* subr_ge0 is defined earlier *)

Lemma subr_le0  x y : (y - x <= 0) = (y <= x).
Proof. by rewrite -subr_ge0 opprB add0r subr_ge0. Qed.

Lemma subr_lt0  x y : (y - x < 0) = (y < x).
Proof. by rewrite -subr_gt0 opprB add0r subr_gt0. Qed.

Definition subr_lte0 := (subr_le0, subr_lt0).
Definition subr_gte0 := (subr_ge0, subr_gt0).
Definition subr_cp0 := (subr_lte0, subr_gte0).

Lemma ltr_asym x y : x < y < x = false.
Proof. by apply/negP=> /andP [/ltr_trans hyx /hyx]; rewrite ltrr. Qed.

Lemma ler_anti : antisymmetric (@ler R).
Proof. by move=> x y; rewrite -eqr_le=> /eqP. Qed.

Lemma ltr_le_asym x y : x < y <= x = false.
Proof. by rewrite ltr_neqAle -andbA -eqr_le eq_sym; case: (_ == _). Qed.

Lemma ler_lt_asym x y : x <= y < x = false.
Proof. by rewrite andbC ltr_le_asym. Qed.

Definition lter_anti := (=^~ eqr_le, ltr_asym, ltr_le_asym, ler_lt_asym).

Lemma ltr_geF x y : x < y -> (y <= x = false).
Proof.
by move=> xy; apply: contraTF isT=> /(ltr_le_trans xy); rewrite ltrr.
Qed.

Lemma ler_gtF x y : x <= y -> (y < x = false).
Proof. by apply: contraTF=> /ltr_geF->. Qed.

Definition ltr_gtF x y hxy := ler_gtF (@ltrW x y hxy).

End PIntegralDomainTheory.

Hint Resolve ler01.
Implicit Arguments ler01 [R].
Hint Resolve lerr.
Hint Resolve ltr01.
Implicit Arguments ltr01 [R].
Hint Resolve ltrr.
Hint Resolve ltrW.
Hint Resolve ltr_eqF.
Hint Resolve ltr0Sn.
Hint Resolve ler0n.
Hint Resolve normr_ge0.

Section PIntegralDomainMonotonyTheory.

Variables R R' : PIntegralDomain.type.
Implicit Types m n p : nat.
Implicit Types x y z : R.
Implicit Types u v w : R'.

Section RR'.

Variable D D' : pred R.
Variable (f : R -> R').

Lemma ltrW_homo (mf : {homo f : x y / x < y}) : {homo f : x y / x <= y}.
Proof. by move=> x y /=; rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW //]. Qed.

Lemma ltrW_nhomo (mf : {homo f : x y /~ x < y}) : {homo f : x y /~ x <= y}.
Proof. by move=> x y /=; rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW //]. Qed.

Lemma homo_inj_lt (fI : injective f) (mf : {homo f : x y / x <= y}) : {homo f : x y / x < y}.
Proof. by move=> x y /= hxy; rewrite ltr_neqAle (inj_eq fI) mf (ltr_eqF, ltrW). Qed.

Lemma nhomo_inj_lt (fI : injective f) (mf : {homo f : x y /~ x <= y}) : {homo f : x y /~ x < y}.
Proof. by move=> x y /= hxy; rewrite ltr_neqAle (inj_eq fI) mf (gtr_eqF, ltrW). Qed.

Lemma mono_inj (mf : {mono f : x y / x <= y}) : injective f.
Proof. by move=> x y /eqP; rewrite eqr_le !mf -eqr_le=> /eqP. Qed.

Lemma nmono_inj (mf : {mono f : x y /~ x <= y}) : injective f.
Proof. by move=> x y /eqP; rewrite eqr_le !mf -eqr_le=> /eqP. Qed.

Lemma lerW_mono (mf : {mono f : x y / x <= y}) : {mono f : x y / x < y}.
Proof.
by move=> x y /=; rewrite !ltr_neqAle mf inj_eq //; apply: mono_inj.
Qed.

Lemma lerW_nmono (mf : {mono f : x y /~ x <= y}) : {mono f : x y /~ x < y}.
Proof.
by move=> x y /=; rewrite !ltr_neqAle mf eq_sym inj_eq //; apply: nmono_inj.
Qed.

(* Monotony in D D' *)
Lemma ltrW_homo_in (mf : {in D & D', {homo f : x y / x < y}}) : {in D & D', {homo f : x y / x <= y}}.
Proof.
by move=> x y hx hy /=; rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW] //; apply.
Qed.

Lemma ltrW_nhomo_in (mf : {in D & D', {homo f : x y /~ x < y}}) :
  {in D & D', {homo f : x y /~ x <= y}}.
Proof.
by move=> x y hx hy /=; rewrite ler_eqVlt=> /orP [/eqP->|/mf /ltrW] //; apply.
Qed.

Lemma homo_inj_in_lt (fI : {in D & D', injective f})
  (mf : {in D & D', {homo f : x y / x <= y}}) : {in D & D', {homo f : x y / x < y}}.
Proof.
move=> x y hx hy /= hxy; rewrite ltr_neqAle; apply/andP; split.
  by apply: contraTN hxy => /eqP /fI -> //; rewrite ltrr.
by rewrite mf // (ltr_eqF, ltrW).
Qed.

Lemma nhomo_inj_in_lt (fI : {in D & D', injective f})
  (mf : {in D & D', {homo f : x y /~ x <= y}}) : {in D & D', {homo f : x y /~ x < y}}.
Proof.
move=> x y hx hy /= hxy; rewrite ltr_neqAle; apply/andP; split.
  by apply: contraTN hxy => /eqP /fI -> //; rewrite ltrr.
by rewrite mf // (gtr_eqF, ltrW).
Qed.

Lemma mono_inj_in (mf : {in D &, {mono f : x y / x <= y}}) : {in D &, injective f}.
Proof. by move=> x y hx hy /= /eqP; rewrite eqr_le !mf // -eqr_le=> /eqP. Qed.

Lemma nmono_inj_in
 (mf : {in D &, {mono f : x y /~ x <= y}}) : {in D &, injective f}.
Proof. by move=> x y hx hy /= /eqP; rewrite eqr_le !mf // -eqr_le=> /eqP. Qed.

Lemma lerW_mono_in (mf : {in D &, {mono f : x y / x <= y}}) : {in D &, {mono f : x y / x < y}}.
Proof.
move=> x y hx hy /=; rewrite !ltr_neqAle mf // (@inj_in_eq _ _ D) //.
exact: mono_inj_in.
Qed.

Lemma lerW_nmono_in (mf : {in D &, {mono f : x y /~ x <= y}}) : {in D &, {mono f : x y /~ x < y}}.
Proof.
move=> x y hx hy /=; rewrite !ltr_neqAle mf // eq_sym (@inj_in_eq _ _ D) //.
exact: nmono_inj_in.
Qed.

End RR'.

Section natR.

Variable (f : nat -> R).

Lemma ltn_ltrW_homo (mf : {homo f : m n / (m < n)%N >-> m < n}) :
  {homo f : m n / (m <= n)%N >-> m <= n}.
Proof. by move=> m n /=; rewrite leq_eqVlt=> /orP [/eqP->|/mf /ltrW //]. Qed.

Lemma ltn_ltrW_nhomo (mf : {homo f : m n / (n < m)%N >-> m < n}) :
  {homo f : m n / (n <= m)%N >-> m <= n}.
Proof. by move=> m n /=; rewrite leq_eqVlt=> /orP [/eqP->|/mf /ltrW //]. Qed.

Lemma homo_inj_ltn_lt (fI : injective f) (mf : {homo f : m n / (m <= n)%N >-> m <= n}) :
  {homo f : m n / (m < n)%N >-> m < n}.
Proof.
move=> m n /= hmn.
by rewrite ltr_neqAle (inj_eq fI) mf ?neq_ltn ?hmn ?orbT // ltnW.
Qed.

Lemma nhomo_inj_ltn_lt (fI : injective f) (mf : {homo f : m n / (n <= m)%N >-> m <= n}) :
  {homo f : m n / (n < m)%N >-> m < n}.
Proof.
by move=> m n /= hmn; rewrite ltr_def (inj_eq fI) mf ?neq_ltn ?hmn // ltnW.
Qed.

Lemma leq_mono_inj (mf : {mono f : m n / (m <= n)%N >-> m <= n}) : injective f.
Proof. by move=> m n /eqP; rewrite eqr_le !mf -eqn_leq=> /eqP. Qed.

Lemma leq_nmono_inj (mf : {mono f : m n / (n <= m)%N >-> m <= n}) : injective f.
Proof. by move=> m n /eqP; rewrite eqr_le !mf -eqn_leq=> /eqP. Qed.

Lemma leq_lerW_mono (mf : {mono f : m n / (m <= n)%N >-> m <= n}) :
  {mono f : m n / (m < n)%N >-> m < n}.
Proof.
move=> m n /=; rewrite !ltr_neqAle mf inj_eq ?ltn_neqAle 1?eq_sym //.
exact: leq_mono_inj.
Qed.

Lemma leq_lerW_nmono (mf : {mono f : m n / (n <= m)%N >-> m <= n}) :
  {mono f : m n / (n < m)%N >-> m < n}.
Proof.
move=> x y /=; rewrite ltr_neqAle mf eq_sym inj_eq ?ltn_neqAle 1?eq_sym //.
exact: leq_nmono_inj.
Qed.

Lemma homo_leq_mono (mf : {homo f : m n / (m < n)%N >-> m < n}) :
  {mono f : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> m n /=; case: leqP; last by move=> /mf /ltr_geF.
by rewrite leq_eqVlt=> /orP [/eqP->|/mf /ltrW //]; rewrite lerr.
Qed.

Lemma nhomo_leq_mono (mf : {homo f : m n / (n < m)%N >-> m < n}) :
  {mono f : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> m n /=; case: leqP; last by move=> /mf /ltr_geF.
by rewrite leq_eqVlt=> /orP [/eqP->|/mf /ltrW //]; rewrite lerr.
Qed.

End natR.

End PIntegralDomainMonotonyTheory.

Section PIntegralDomainOperationTheory.
(* Comparision and opposite *)

Variable R : PIntegralDomain.type.
Implicit Types x y z t : R.

Lemma ler_opp2 : {mono -%R : x y /~ x <= y :> R}.
Proof. by move=> x y /=; rewrite -subr_ge0 opprK addrC subr_ge0. Qed.
Hint Resolve ler_opp2.

Lemma ltr_opp2 : {mono -%R : x y /~ x < y :> R}.
Proof. by move=> x y /=; rewrite lerW_nmono. Qed.
Hint Resolve ltr_opp2.

Definition lter_opp2 := (ler_opp2, ltr_opp2).

Lemma ler_oppr x y : (x <= - y) = (y <= - x).
Proof. by rewrite (monoRL (@opprK _) ler_opp2). Qed.

Lemma ltr_oppr x y : (x < - y) = (y < - x).
Proof. by rewrite (monoRL (@opprK _) (lerW_nmono _)). Qed.

Definition lter_oppr := (ler_oppr, ltr_oppr).

Lemma ler_oppl x y : (- x <= y) = (- y <= x).
Proof. by rewrite (monoLR (@opprK _) ler_opp2). Qed.

Lemma ltr_oppl x y : (- x < y) = (- y < x).
Proof. by rewrite (monoLR (@opprK _) (lerW_nmono _)). Qed.

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

(* norm theory*)

Lemma ler0_norm x : x <= 0 -> `|x| = - x.
Proof. by move=> x_le0; rewrite -[RHS]ger0_norm ?normrN ?oppr_ge0. Qed.

Definition gtr0_norm x (hx : 0 < x) := ger0_norm (ltrW hx).
Definition ltr0_norm x (hx : x < 0) := ler0_norm (ltrW hx).

Lemma normr_le0 x : (`|x| <= 0) = (x == 0).
Proof. by rewrite -normr_eq0 eqr_le normr_ge0 andbT. Qed.

Lemma normr_lt0 x : `|x| < 0 = false.
Proof. by rewrite ltr_neqAle normr_le0 normr_eq0 andNb. Qed.

Lemma normr_gt0 x : (`|x| > 0) = (x != 0).
Proof. by rewrite ltr_def normr_eq0 normr_ge0 andbT. Qed.

Definition normrE x := (normr_id, normr0, normr1, normrN1, normr_ge0, normr_eq0,
  normr_lt0, normr_le0, normr_gt0, normrN).

Lemma normrX n x : `|x ^+ n| = `|x| ^+ n.
Proof. by elim: n=> [|n ihn]; rewrite ?normr1 // !exprS normrM ihn. Qed.

(* real theory *)

Lemma realE x : (x \in real) = (0 <= x) || (x <= 0). Proof. by []. Qed.

Lemma ger0_real x : 0 <= x -> x \in real.
Proof. by rewrite realE => ->. Qed.

Lemma ler0_real x : x <= 0 -> x \in real.
Proof. by rewrite realE orbC => ->. Qed.

Lemma real0 : 0 \in (@Rreal R). Proof. by rewrite realE lerr. Qed.
Hint Resolve real0.

Lemma real1 : 1 \in (@Rreal R). Proof. by rewrite realE ler01. Qed.
Hint Resolve real1.

Lemma realn n : n%:R \in (@Rreal R). Proof. by rewrite realE ler0n. Qed.

Lemma ler_leVge x y : x <= 0 -> y <= 0 -> (x <= y) || (y <= x).
Proof. by rewrite -!oppr_ge0 => /(ger_leVge _) h /h; rewrite !ler_opp2. Qed.

Lemma real_leVge x y : x \in real -> y \in real -> (x <= y) || (y <= x).
Proof.
rewrite !realE; have [x_ge0 _|x_nge0 /= x_le0] := boolP (_ <= _); last first.
  by have [/(ler_trans x_le0)->|_ /(ler_leVge x_le0) //] := boolP (0 <= _).
by have [/(ger_leVge x_ge0)|_ /ler_trans->] := boolP (0 <= _); rewrite ?orbT.
Qed.

Lemma realB : {in real &, forall x y, x - y \in real}.
Proof. by move=> x y xR yR /=; rewrite realE !subr_cp0 real_leVge. Qed.

Lemma realN : {mono (@GRing.opp R) : x /  x \in real}.
Proof.
move=> x /=; have [xR|] := boolP (x \in _); first by rewrite -sub0r realB.
by apply: contraNF=> NxR; rewrite -[x]opprK -sub0r realB.
Qed.

Lemma realBC x y : (x - y \in real) = (y - x \in real).
Proof. by rewrite -realN opprB. Qed.

Lemma realD : {in real &, forall x y, x + y \in real}.
Proof. by move=> x y xR yR /=; rewrite -[y]opprK realB ?realN. Qed.

Lemma add_real_l x y : x \in real -> (x + y \in real) = (y \in real).
Proof.
move=> xR; have [yR|] := boolP (y \in _); first by rewrite realD.
by apply: contraNF=> xyR; rewrite -(addrK x y) realB // addrC.
Qed.

Lemma add_real_r x y : y \in real -> (x + y \in real) = (x \in real).
Proof. by move=> yR; rewrite addrC add_real_l. Qed.

(* dichotomy and trichotomy *)

CoInductive ler_xor_gt (x y : R) : R -> R -> bool -> bool -> Set :=
  | LerNotGt of x <= y : ler_xor_gt x y (y - x) (y - x) true false
  | GtrNotLe of y < x  : ler_xor_gt x y (x - y) (x - y) false true.

CoInductive ltr_xor_ge (x y : R) : R -> R -> bool -> bool -> Set :=
  | LtrNotGe of x < y  : ltr_xor_ge x y (y - x) (y - x) false true
  | GerNotLt of y <= x : ltr_xor_ge x y (x - y) (x - y) true false.

CoInductive cparer x y : R -> R ->
  bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CparerLt of x < y : cparer x y (y - x) (y - x)
    false false true false true false
  | CparerGt of x > y : cparer x y (x - y) (x - y)
    false false false true false true
  | CparerEq of x = y : cparer x y 0 0
    true true true true false false.

Lemma real_lerP x y : x \in real -> y \in real ->
  ler_xor_gt x y `|x - y| `|y - x| (x <= y) (y < x).
Proof.
move=> xR /(real_leVge xR); have [le_xy _|Nle_xy /= le_yx] := boolP (_ <= _).
  have [/(ler_lt_trans le_xy)|] := boolP (_ < _); first by rewrite ltrr.
  by rewrite ler0_norm ?ger0_norm ?subr_cp0 ?opprB //; constructor.
have [lt_yx|] := boolP (_ < _).
  by rewrite ger0_norm ?ler0_norm ?subr_cp0 ?opprB //; constructor.
by rewrite ltr_def le_yx andbT negbK=> /eqP exy; rewrite exy lerr in Nle_xy.
Qed.

Lemma real_ltrP x y : x \in real -> y \in real ->
  ltr_xor_ge x y `|x - y| `|y - x| (y <= x) (x < y).
Proof. by move=> xR yR; case: real_lerP=> //; constructor. Qed.

Lemma real_ltrNge : {in real &, forall x y, (x < y) = ~~ (y <= x)}.
Proof. by move=> x y xR yR /=; case: real_lerP. Qed.

Lemma real_lerNgt : {in real &, forall x y, (x <= y) = ~~ (y < x)}.
Proof. by move=> x y xR yR /=; case: real_lerP. Qed.

Lemma real_ltrgtP x y : x \in real -> y \in real ->
  cparer x y `|x - y| `|y - x| (y == x) (x == y) (x <= y) (y <= x) (x < y) (x > y).
Proof.
move=> xR yR; case: real_lerP => // [le_yx|lt_xy]; last first.
  by rewrite gtr_eqF // ltr_eqF // ler_gtF ?ltrW //; constructor.
case: real_lerP => // [le_xy|lt_yx]; last first.
  by rewrite ltr_eqF // gtr_eqF //; constructor.
have /eqP ->: x == y by rewrite eqr_le le_yx le_xy.
by rewrite subrr eqxx; constructor.
Qed.

CoInductive ger0_xor_lt0 (x : R) : R -> bool -> bool -> Set :=
  | Ger0NotLt0 of 0 <= x : ger0_xor_lt0 x x false true
  | Ltr0NotGe0 of x < 0  : ger0_xor_lt0 x (- x) true false.

CoInductive ler0_xor_gt0 (x : R) : R -> bool -> bool -> Set :=
  | Ler0NotLe0 of x <= 0 : ler0_xor_gt0 x (- x) false true
  | Gtr0NotGt0 of 0 < x  : ler0_xor_gt0 x x true false.

CoInductive cparer0 x : R -> bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CparerGt0 of 0 < x : cparer0 x x false false false true false true
  | CparerLt0 of x < 0 : cparer0 x (- x) false false true false true false
  | CparerEq0 of x = 0 : cparer0 x 0 true true true true false false.

Lemma real_ger0P x : x \in real -> ger0_xor_lt0 x `|x| (x < 0) (0 <= x).
Proof.
move=> hx; rewrite -{2}[x]subr0; case: real_ltrP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_ler0P x : x \in real -> ler0_xor_gt0 x `|x| (0 < x) (x <= 0).
Proof.
move=> hx; rewrite -{2}[x]subr0; case: real_ltrP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_ltrgt0P x : x \in real ->
  cparer0 x `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof.
move=> hx; rewrite -{2}[x]subr0; case: real_ltrgtP;
by rewrite ?subr0 ?sub0r //; constructor.
Qed.

Lemma real_neqr_lt : {in real &, forall x y, (x != y) = (x < y) || (y < x)}.
Proof. by move=> * /=; case: real_ltrgtP. Qed.

Lemma ler_sub_real x y : x <= y -> y - x \in real.
Proof. by move=> le_xy; rewrite ger0_real // subr_ge0. Qed.

Lemma ger_sub_real x y : x <= y -> x - y \in real.
Proof. by move=> le_xy; rewrite ler0_real // subr_le0. Qed.

Lemma ler_real y x : x <= y -> (x \in real) = (y \in real).
Proof. by move=> le_xy; rewrite -(addrNK x y) add_real_l ?ler_sub_real. Qed.

Lemma ger_real x y : y <= x -> (x \in real) = (y \in real).
Proof. by move=> le_yx; rewrite -(ler_real le_yx). Qed.

Lemma ger1_real x : 1 <= x -> x \in real. Proof. by move=> /ger_real->. Qed.
Lemma ler1_real x : x <= 1 -> x \in real. Proof. by move=> /ler_real->. Qed.

Lemma Nreal_leF x y : y \in real -> x \notin real -> (x <= y) = false.
Proof. by move=> yR; apply: contraNF=> /ler_real->. Qed.

Lemma Nreal_geF x y : y \in real -> x \notin real -> (y <= x) = false.
Proof. by move=> yR; apply: contraNF=> /ger_real->. Qed.

Lemma Nreal_ltF x y : y \in real -> x \notin real -> (x < y) = false.
Proof. by move=> yR xNR; rewrite ltr_def Nreal_leF ?andbF. Qed.

Lemma Nreal_gtF x y : y \in real -> x \notin real -> (y < x) = false.
Proof. by move=> yR xNR; rewrite ltr_def Nreal_geF ?andbF. Qed.

(* real wlog *)

Lemma real_wlog_ler P : (forall a b, P b a -> P a b)
  -> (forall a b, a <= b -> P a b) ->
  forall a b : R, a \in real -> b \in real -> P a b.
Proof.
move=> sP hP a b ha hb; wlog: a b ha hb / a <= b=> [hwlog|]; last exact: hP.
by case: (real_lerP ha hb)=> [/hP //|/ltrW hba]; apply: sP; apply: hP.
Qed.

Lemma real_wlog_ltr P : (forall a, P a a) -> (forall a b, (P b a -> P a b))
  -> (forall a b, a < b -> P a b) ->
  forall a b : R, a \in real -> b \in real -> P a b.
Proof.
move=> rP sP hP; apply: real_wlog_ler=> // a b.
by rewrite ler_eqVlt; case: (altP (_ =P _))=> [->|] //= _ lab; apply: hP.
Qed.

(* Monotony of addition *)
Lemma ler_add2l x : {mono +%R x : y z / y <= z}.
Proof.
by move=> y z /=; rewrite -subr_ge0 opprD addrAC addNKr addrC subr_ge0.
Qed.

Lemma ler_add2r x : {mono +%R^~ x : y z / y <= z}.
Proof. by move=> y z /=; rewrite ![_ + x]addrC ler_add2l. Qed.

Lemma ltr_add2r z x y : (x + z < y + z) = (x < y).
Proof. by rewrite (lerW_mono (ler_add2r _)). Qed.

Lemma ltr_add2l z x y : (z + x < z + y) = (x < y).
Proof. by rewrite (lerW_mono (ler_add2l _)). Qed.

Definition ler_add2 := (ler_add2l, ler_add2r).
Definition ltr_add2 := (ltr_add2l, ltr_add2r).
Definition lter_add2 := (ler_add2, ltr_add2).

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
Proof. by rewrite (monoLR (addrK _) (ler_add2r _)). Qed.

Lemma ltr_subl_addr x y z : (x - y < z) = (x < z + y).
Proof. by rewrite (monoLR (addrK _) (ltr_add2r _)). Qed.

Lemma ler_subr_addr x y z : (x <= y - z) = (x + z <= y).
Proof. by rewrite (monoLR (addrNK _) (ler_add2r _)). Qed.

Lemma ltr_subr_addr x y z : (x < y - z) = (x + z < y).
Proof. by rewrite (monoLR (addrNK _) (ltr_add2r _)). Qed.

Definition ler_sub_addr := (ler_subl_addr, ler_subr_addr).
Definition ltr_sub_addr := (ltr_subl_addr, ltr_subr_addr).
Definition lter_sub_addr := (ler_sub_addr, ltr_sub_addr).

Lemma ler_subl_addl x y z : (x - y <= z) = (x <= y + z).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ltr_subl_addl x y z : (x - y < z) = (x < y + z).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ler_subr_addl x y z : (x <= y - z) = (z + x <= y).
Proof. by rewrite lter_sub_addr addrC. Qed.

Lemma ltr_subr_addl x y z : (x < y - z) = (z + x < y).
Proof. by rewrite lter_sub_addr addrC. Qed.

Definition ler_sub_addl := (ler_subl_addl, ler_subr_addl).
Definition ltr_sub_addl := (ltr_subl_addl, ltr_subr_addl).
Definition lter_sub_addl := (ler_sub_addl, ltr_sub_addl).

Lemma ler_addl x y : (x <= x + y) = (0 <= y).
Proof. by rewrite -{1}[x]addr0 lter_add2. Qed.

Lemma ltr_addl x y : (x < x + y) = (0 < y).
Proof. by rewrite -{1}[x]addr0 lter_add2. Qed.

Lemma ler_addr x y : (x <= y + x) = (0 <= y).
Proof. by rewrite -{1}[x]add0r lter_add2. Qed.

Lemma ltr_addr x y : (x < y + x) = (0 < y).
Proof. by rewrite -{1}[x]add0r lter_add2. Qed.

Lemma ger_addl x y : (x + y <= x) = (y <= 0).
Proof. by rewrite -{2}[x]addr0 lter_add2. Qed.

Lemma gtr_addl x y : (x + y < x) = (y < 0).
Proof. by rewrite -{2}[x]addr0 lter_add2. Qed.

Lemma ger_addr x y : (y + x <= x) = (y <= 0).
Proof. by rewrite -{2}[x]add0r lter_add2. Qed.

Lemma gtr_addr x y : (y + x < x) = (y < 0).
Proof. by rewrite -{2}[x]add0r lter_add2. Qed.

Definition cpr_add := (ler_addl, ler_addr, ger_addl, ger_addl,
                       ltr_addl, ltr_addr, gtr_addl, gtr_addl).

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

(* x and y have the same sign and their sum is null *)
Lemma paddr_eq0 (x y : R) : 0 <= x -> 0 <= y ->
  (x + y == 0) = (x == 0) && (y == 0).
Proof.
rewrite le0r; case/orP=> [/eqP->|hx]; first by rewrite add0r eqxx.
by rewrite (gtr_eqF hx) /= => hy; rewrite gtr_eqF // ltr_spaddl.
Qed.

Lemma naddr_eq0 (x y : R) (hx : x <= 0) (hy : y <= 0) :
  (x + y == 0) = (x == 0) && (y == 0).
Proof. by rewrite -oppr_eq0 opprD paddr_eq0 ?oppr_cp0 // !oppr_eq0. Qed.

Lemma addr_ss_eq0 (x y : R) : (0 <= x) && (0 <= y) || (x <= 0) && (y <= 0) ->
  (x + y == 0) = (x == 0) && (y == 0).
Proof. by case/orP=> /andP []; [apply: paddr_eq0|apply: naddr_eq0]. Qed.

(* big sum and ler *)
Lemma sumr_ge0 I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> (0 <= F i)) -> 0 <= \sum_(i <- r | P i) (F i).
Proof. exact: (big_ind _ _ (@ler_paddl 0)). Qed.

Lemma ler_sum I (r : seq I) (P : pred I) (F G : I -> R) :
  (forall i, P i -> F i <= G i) ->
  (\sum_(i <- r | P i) F i) <= \sum_(i <- r | P i) G i.
Proof. exact: (big_ind2 _ (lerr _) ler_add). Qed.

Lemma psumr_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof.
elim: r=> [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
by case: ifP=> pa /=; rewrite ?paddr_eq0 ?ihr ?hr // sumr_ge0.
Qed.

(* mulr and ler/ltr *)

Lemma ler_pmul2l x (hx : 0 < x) : {mono *%R x : x y / x <= y}.
Proof. by move=> y z /=; rewrite -subr_ge0 -mulrBr pmulr_rge0 // subr_ge0. Qed.

Lemma ltr_pmul2l x (hx : 0 < x) : {mono *%R x : x y / x < y}.
Proof. exact: lerW_mono (ler_pmul2l _). Qed.

Definition lter_pmul2l := (ler_pmul2l, ltr_pmul2l).

Lemma ler_pmul2r x (hx : 0 < x) : {mono *%R^~ x : x y / x <= y}.
Proof. by move=> y z /=; rewrite ![_ * x]mulrC ler_pmul2l. Qed.

Lemma ltr_pmul2r x (hx : 0 < x) : {mono *%R^~ x : x y / x < y}.
Proof. exact: lerW_mono (ler_pmul2r _). Qed.

Definition lter_pmul2r := (ler_pmul2r, ltr_pmul2r).

Lemma ler_nmul2l x (hx : x < 0) : {mono *%R x : x y /~ x <= y}.
Proof. by move=> y z /=; rewrite -ler_opp2 -!mulNr ler_pmul2l ?oppr_gt0. Qed.

Lemma ltr_nmul2l x (hx : x < 0) : {mono *%R x : x y /~ x < y}.
Proof. exact: lerW_nmono (ler_nmul2l _). Qed.

Definition lter_nmul2l := (ler_nmul2l, ltr_nmul2l).

Lemma ler_nmul2r x (hx : x < 0) : {mono *%R^~ x : x y /~ x <= y}.
Proof. by move=> y z /=; rewrite ![_ * x]mulrC ler_nmul2l. Qed.

Lemma ltr_nmul2r x (hx : x < 0) : {mono *%R^~ x : x y /~ x < y}.
Proof. exact: lerW_nmono (ler_nmul2r _). Qed.

Definition lter_nmul2r := (ler_nmul2r, ltr_nmul2r).

Lemma ler_wpmul2l x : 0 <= x -> {homo *%R x : y z / y <= z}.
Proof.
by rewrite le0r=> /orP [/eqP-> ??|/ler_pmul2l /mono2W //]; rewrite !mul0r.
Qed.

Lemma ler_wpmul2r x (hx : 0 <= x) : {homo *%R^~ x : y z / y <= z}.
Proof. by move=> /= *; rewrite ![_ * x]mulrC ler_wpmul2l. Qed.

Lemma ler_wnmul2l x (hx : x <= 0) : {homo *%R x : x y /~ x <= y}.
Proof. by move=> /= *; rewrite -![x * _]mulrNN ler_wpmul2l ?lter_oppE. Qed.

Lemma ler_wnmul2r x (hx : x <= 0) : {homo *%R^~ x : x y /~ x <= y}.
Proof. by move=> /= *; rewrite -![_ * x]mulrNN ler_wpmul2r ?lter_oppE. Qed.

(* complement for x *+ n and <= or < *)

Lemma ler_pmuln2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x <= y}.
Proof.
by case: n=> // n _ x y /=; rewrite -mulr_natl -[y *+ _]mulr_natl ler_pmul2l.
Qed.

Lemma ltr_pmuln2r n : (0 < n)%N -> {mono (@GRing.natmul R)^~ n : x y / x < y}.
Proof. by move=> n_gt0; apply: lerW_mono (ler_pmuln2r _). Qed.

Lemma pmulrn_lgt0 x n (n0 : (0 < n)%N) : 0 < x *+ n = (0 < x).
Proof. by rewrite -(mul0rn _ n) ltr_pmuln2r // mul0rn. Qed.

Lemma pmulrn_llt0 x n (n0 : (0 < n)%N) : x *+ n < 0 = (x < 0).
Proof. by rewrite -(mul0rn _ n) ltr_pmuln2r // mul0rn. Qed.

Lemma pmulrn_lge0 x n (n0 : (0 < n)%N) : 0 <= x *+ n = (0 <= x).
Proof. by rewrite -(mul0rn _ n) ler_pmuln2r // mul0rn. Qed.

Lemma pmulrn_lle0 x n (n0 : (0 < n)%N) : x *+ n <= 0 = (x <= 0).
Proof. by rewrite -(mul0rn _ n) ler_pmuln2r // mul0rn. Qed.

Lemma ltr_wmuln2r x y n (hxy : x < y) : x *+ n < y *+ n = (0 < n)%N.
Proof. by case: n=> // n; rewrite ltr_pmuln2r. Qed.

Lemma ltr_wpmuln2r n : (0 < n)%N -> {homo (@GRing.natmul R)^~ n : x y / x < y}.
Proof. by move=> hn x y /= / ltr_wmuln2r ->. Qed.

Lemma ler_wmuln2r n : {homo (@GRing.natmul R)^~ n : x y / x <= y}.
Proof. by move=> x y hxy /=; case: n=> // n; rewrite ler_pmuln2r. Qed.

Lemma mulrn_wge0 x n : 0 <= x -> 0 <= x *+ n.
Proof. by move=> /(ler_wmuln2r n); rewrite mul0rn. Qed.

Lemma mulrn_wle0 x n : x <= 0 -> x *+ n <= 0.
Proof. by move=> /(ler_wmuln2r n); rewrite mul0rn. Qed.

Lemma ler_muln2r n x y : (x *+ n <= y *+ n) = ((n == 0%N) || (x <= y)).
Proof. by case: n=> [|n]; rewrite ?lerr ?eqxx // ler_pmuln2r. Qed.

Lemma ltr_muln2r n x y : (x *+ n < y *+ n) = ((0 < n)%N && (x < y)).
Proof. by case: n=> [|n]; rewrite ?lerr ?eqxx // ltr_pmuln2r. Qed.

(* Characteristic is null *)

Lemma char_po : [char R] =i pred0.
Proof. by case=> // p /=; rewrite !inE pnatr_eq0 andbF. Qed.

Lemma mulrn_eq0 x n : (x *+ n == 0) = ((n == 0)%N || (x == 0)).
Proof. by rewrite -mulr_natl mulf_eq0 pnatr_eq0. Qed.

Lemma mulrIn x : x != 0 -> injective (GRing.natmul x).
Proof.
move=> x_neq0; apply: wlog_leq=> m n; first by move=> hx hab; rewrite hx.
move/eqP; rewrite eq_sym -subr_eq0 -mulrnBr ?leq_addr // addnC addnK.
by rewrite mulrn_eq0 (negPf x_neq0) orbF => /eqP->.
Qed.

Lemma ler_wpmuln2l x (hx : 0 <= x) :
  {homo (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof. by move=> m n /subnK <-; rewrite mulrnDr ler_paddl ?mulrn_wge0. Qed.

Lemma ler_wnmuln2l x (hx : x <= 0) :
  {homo (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> m n hmn /=; rewrite -ler_opp2 -!mulNrn ler_wpmuln2l // oppr_cp0.
Qed.

Lemma mulrn_wgt0 x n : 0 < x -> 0 < x *+ n = (0 < n)%N.
Proof. by case: n=> // n hx; rewrite pmulrn_lgt0. Qed.

Lemma mulrn_wlt0 x n : x < 0 -> x *+ n < 0 = (0 < n)%N.
Proof. by case: n=> // n hx; rewrite pmulrn_llt0. Qed.

Lemma ler_pmuln2l x (hx : 0 < x) :
  {mono (@GRing.natmul R x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> m n /=; case: leqP => hmn; first by rewrite ler_wpmuln2l // ltrW.
rewrite -(subnK (ltnW hmn)) mulrnDr ger_addr ltr_geF //.
by rewrite mulrn_wgt0 // subn_gt0.
Qed.

Lemma ltr_pmuln2l x (hx : 0 < x) :
  {mono (@GRing.natmul R x) : m n / (m < n)%N >-> m < n}.
Proof. exact: leq_lerW_mono (ler_pmuln2l _). Qed.

Lemma ler_nmuln2l x (hx : x < 0) :
  {mono (@GRing.natmul R x) : m n / (n <= m)%N >-> m <= n}.
Proof.
by move=> m n /=; rewrite -ler_opp2 -!mulNrn ler_pmuln2l // oppr_gt0.
Qed.

Lemma ltr_nmuln2l x (hx : x < 0) :
  {mono (@GRing.natmul R x) : m n / (n < m)%N >-> m < n}.
Proof. exact: leq_lerW_nmono (ler_nmuln2l _). Qed.

Lemma ler_nat m n : (m%:R <= n%:R :> R) = (m <= n)%N.
Proof. by rewrite ler_pmuln2l. Qed.

Lemma ltr_nat m n : (m%:R < n%:R :> R) = (m < n)%N.
Proof. by rewrite ltr_pmuln2l. Qed.

Lemma eqr_nat  m n : (m%:R == n%:R :> R) = (m == n)%N.
Proof. by rewrite (inj_eq (mulrIn _)) ?oner_eq0. Qed.

Lemma lern0 n : (n%:R <= 0 :> R) = (n == 0%N).
Proof. by rewrite -[0]/0%:R ler_nat leqn0. Qed.

Lemma ltrn0 n : (n%:R < 0 :> R) = false.
Proof. by rewrite -[0]/0%:R ltr_nat ltn0. Qed.

Lemma ler1n n : 1 <= n%:R :> R = (1 <= n)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltr1n n : 1 < n%:R :> R = (1 < n)%N. Proof. by rewrite -ltr_nat. Qed.
Lemma lern1 n : n%:R <= 1 :> R = (n <= 1)%N. Proof. by rewrite -ler_nat. Qed.
Lemma ltrn1 n : n%:R < 1 :> R = (n < 1)%N. Proof. by rewrite -ltr_nat. Qed.

Lemma ltrN10 : -1 < 0 :> R. Proof. by rewrite oppr_lt0. Qed.
Lemma lerN10 : -1 <= 0 :> R. Proof. by rewrite oppr_le0. Qed.
Lemma ltr10 : 1 < 0 :> R = false. Proof. by rewrite ler_gtF. Qed.
Lemma ler10 : 1 <= 0 :> R = false. Proof. by rewrite ltr_geF. Qed.
Lemma ltr0N1 : 0 < -1 :> R = false. Proof. by rewrite ler_gtF // lerN10. Qed.
Lemma ler0N1 : 0 <= -1 :> R = false. Proof. by rewrite ltr_geF // ltrN10. Qed.

Lemma pmulrn_rgt0 x n (x0 : 0 < x) : 0 < x *+ n = (0 < n)%N.
Proof. by rewrite -(mulr0n x) ltr_pmuln2l. Qed.

Lemma pmulrn_rlt0 x n (x0 : 0 < x) : x *+ n < 0 = false.
Proof. by rewrite -(mulr0n x) ltr_pmuln2l. Qed.

Lemma pmulrn_rge0 x n (x0 : 0 < x) : 0 <= x *+ n.
Proof. by rewrite -(mulr0n x) ler_pmuln2l. Qed.

Lemma pmulrn_rle0 x n (x0 : 0 < x) : x *+ n <= 0 = (n == 0)%N.
Proof. by rewrite -(mulr0n x) ler_pmuln2l ?leqn0. Qed.

Lemma nmulrn_rgt0 x n (x0 : x < 0) : 0 < x *+ n = false.
Proof. by rewrite -(mulr0n x) ltr_nmuln2l. Qed.

Lemma nmulrn_rge0 x n (x0 : x < 0) : 0 <= x *+ n = (n == 0)%N.
Proof. by rewrite -(mulr0n x) ler_nmuln2l ?leqn0. Qed.

Lemma nmulrn_rle0 x n (x0 : x < 0) : x *+ n <= 0.
Proof. by rewrite -(mulr0n x) ler_nmuln2l. Qed.

(* (x * y) compared to 0 *)
(* Remark : pmulr_rgt0 and pmulr_rge0 are defined above *)

(* x positive and y right *)
Lemma pmulr_rlt0 x y : 0 < x -> (x * y < 0) = (y < 0).
Proof. by move=> x_gt0; rewrite -oppr_gt0 -mulrN pmulr_rgt0 // oppr_gt0. Qed.

Lemma pmulr_rle0 x y : 0 < x -> (x * y <= 0) = (y <= 0).
Proof. by move=> x_gt0; rewrite -oppr_ge0 -mulrN pmulr_rge0 // oppr_ge0. Qed.

(* x positive and y left *)
Lemma pmulr_lgt0 x y : 0 < x -> (0 < y * x) = (0 < y).
Proof. by move=> hx; rewrite mulrC pmulr_rgt0. Qed.

Lemma pmulr_lge0 x y : 0 < x -> (0 <= y * x) = (0 <= y).
Proof. by move=> hx; rewrite mulrC pmulr_rge0. Qed.

Lemma pmulr_llt0 x y : 0 < x -> (y * x < 0) = (y < 0).
Proof. by move=> hx; rewrite mulrC pmulr_rlt0. Qed.

Lemma pmulr_lle0 x y : 0 < x -> (y * x <= 0) = (y <= 0).
Proof. by move=> hx; rewrite mulrC pmulr_rle0. Qed.

(* x negative and y right *)
Lemma nmulr_rgt0 x y : x < 0 -> (0 < x * y) = (y < 0).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rgt0 lter_oppE. Qed.

Lemma nmulr_rge0 x y : x < 0 -> (0 <= x * y) = (y <= 0).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rge0 lter_oppE. Qed.

Lemma nmulr_rlt0 x y : x < 0 -> (x * y < 0) = (0 < y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rlt0 lter_oppE. Qed.

Lemma nmulr_rle0 x y : x < 0 -> (x * y <= 0) = (0 <= y).
Proof. by move=> x_lt0; rewrite -mulrNN pmulr_rle0 lter_oppE. Qed.

(* x negative and y left *)
Lemma nmulr_lgt0 x y : x < 0 -> (0 < y * x) = (y < 0).
Proof. by move=> hx; rewrite mulrC nmulr_rgt0. Qed.

Lemma nmulr_lge0 x y : x < 0 -> (0 <= y * x) = (y <= 0).
Proof. by move=> hx; rewrite mulrC nmulr_rge0. Qed.

Lemma nmulr_llt0 x y : x < 0 -> (y * x < 0) = (0 < y).
Proof. by move=> hx; rewrite mulrC nmulr_rlt0. Qed.

Lemma nmulr_lle0 x y : x < 0 -> (y * x <= 0) = (0 <= y).
Proof. by move=> hx; rewrite mulrC nmulr_rle0. Qed.

(* weak and symmetric lemmas *)
Lemma mulr_ge0 x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. by move=> x_ge0 y_ge0; rewrite -(mulr0 x) ler_wpmul2l. Qed.

Lemma mulr_le0 x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnmul2l. Qed.

Lemma mulr_ge0_le0 x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wpmul2l. Qed.

Lemma mulr_le0_ge0 x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof. by move=> x_le0 y_le0; rewrite -(mulr0 x) ler_wnmul2l. Qed.

(* real of mul *)

Lemma realIr x y : x != 0 -> x \in real -> (x * y \in real) = (y \in real).
Proof.
move=> x_neq0 xR; case: real_ltrgtP x_neq0 => // hx _; rewrite !realE.
* by rewrite nmulr_rge0 // nmulr_rle0 // orbC.
by rewrite pmulr_rge0 // pmulr_rle0 // orbC.
Qed.

Lemma realrI x y : y != 0 -> y \in real -> (x * y \in real) = (x \in real).
Proof. by move=> y_neq0 yR; rewrite mulrC realIr. Qed.

Lemma realM : {in real &, forall x y, x * y \in real}.
Proof.
move=> x y xR yR; have [->|x_neq0] := eqVneq x 0; first by rewrite mul0r.
by rewrite realIr.
Qed.

Lemma realrIn x n : (n != 0)%N -> (x *+ n \in real) = (x \in real).
Proof. by move=> n_neq0; rewrite -mulr_natl realIr ?realn ?pnatr_eq0. Qed.

(* ler/ltr and multiplication between a positive/negative *)

Lemma ger_pmull x y : 0 < y -> (x * y <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_pmul2r. Qed.

Lemma gtr_pmull x y : 0 < y -> (x * y < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_pmul2r. Qed.

Lemma ger_pmulr x y : 0 < y -> (y * x <= y) = (x <= 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_pmul2l. Qed.

Lemma gtr_pmulr x y : 0 < y -> (y * x < y) = (x < 1).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_pmul2l. Qed.

Lemma ler_pmull x y : 0 < y -> (y <= x * y) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_pmul2r. Qed.

Lemma ltr_pmull x y : 0 < y -> (y < x * y) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_pmul2r. Qed.

Lemma ler_pmulr x y : 0 < y -> (y <= y * x) = (1 <= x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_pmul2l. Qed.

Lemma ltr_pmulr x y : 0 < y -> (y < y * x) = (1 < x).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_pmul2l. Qed.

Lemma ger_nmull x y : y < 0 -> (x * y <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ler_nmul2r. Qed.

Lemma gtr_nmull x y : y < 0 -> (x * y < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mul1r ltr_nmul2r. Qed.

Lemma ger_nmulr x y : y < 0 -> (y * x <= y) = (1 <= x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ler_nmul2l. Qed.

Lemma gtr_nmulr x y : y < 0 -> (y * x < y) = (1 < x).
Proof. by move=> hy; rewrite -{2}[y]mulr1 ltr_nmul2l. Qed.

Lemma ler_nmull x y : y < 0 -> (y <= x * y) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ler_nmul2r. Qed.

Lemma ltr_nmull x y : y < 0 -> (y < x * y) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mul1r ltr_nmul2r. Qed.

Lemma ler_nmulr x y : y < 0 -> (y <= y * x) = (x <= 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ler_nmul2l. Qed.

Lemma ltr_nmulr x y : y < 0 -> (y < y * x) = (x < 1).
Proof. by move=> hy; rewrite -{1}[y]mulr1 ltr_nmul2l. Qed.

(* ler/ltr and multiplication between a positive/negative
   and a exterior (1 <= _) or interior (0 <= _ <= 1) *)

Lemma ler_pemull x y : 0 <= y -> 1 <= x -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wpmul2r. Qed.

Lemma ler_nemull x y : y <= 0 -> 1 <= x -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wnmul2r. Qed.

Lemma ler_pemulr x y : 0 <= y -> 1 <= x -> y <= y * x.
Proof. by move=> hy hx; rewrite -{1}[y]mulr1 ler_wpmul2l. Qed.

Lemma ler_nemulr x y : y <= 0 -> 1 <= x -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wnmul2l. Qed.

Lemma ler_pimull x y : 0 <= y -> x <= 1 -> x * y <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mul1r ler_wpmul2r. Qed.

Lemma ler_nimull x y : y <= 0 -> x <= 1 -> y <= x * y.
Proof. by move=> hy hx; rewrite -{1}[y]mul1r ler_wnmul2r. Qed.

Lemma ler_pimulr x y : 0 <= y -> x <= 1 -> y * x <= y.
Proof. by move=> hy hx; rewrite -{2}[y]mulr1 ler_wpmul2l. Qed.

Lemma ler_nimulr x y : y <= 0 -> x <= 1 -> y <= y * x.
Proof. by move=> hx hy; rewrite -{1}[y]mulr1 ler_wnmul2l. Qed.

Lemma mulr_ile1 x y : 0 <= x -> 0 <= y -> x <= 1 -> y <= 1 -> x * y <= 1.
Proof. by move=> *; rewrite (@ler_trans _ y) ?ler_pimull. Qed.

Lemma mulr_ilt1 x y : 0 <= x -> 0 <= y -> x < 1 -> y < 1 -> x * y < 1.
Proof. by move=> *; rewrite (@ler_lt_trans _ y) ?ler_pimull // ltrW. Qed.

Definition mulr_ilte1 := (mulr_ile1, mulr_ilt1).

Lemma mulr_ege1 x y (l1x : 1 <= x) (l1y : 1 <= y) : 1 <= x * y.
Proof. by rewrite (@ler_trans _ y) ?ler_pemull // (ler_trans ler01). Qed.

Lemma mulr_egt1 x y (l1x : 1 < x) (l1y : 1 < y) : 1 < x * y.
Proof. by rewrite (@ltr_trans _ y) // ltr_pmull // (ltr_trans ltr01). Qed.

Definition mulr_egte1 := (mulr_ege1, mulr_egt1).
Definition mulr_cp1 := (mulr_ilte1, mulr_egte1).

(* ler and ^-1 *)

Lemma invr_gt0 x : (0 < x^-1) = (0 < x).
Proof.
have [ux | nux] := boolP (x \in GRing.unit); last by rewrite invr_out.
by apply/idP/idP=> /ltr_pmul2r<-; rewrite mul0r (mulrV, mulVr) ?ltr01.
Qed.

Lemma invr_ge0 x : (0 <= x^-1) = (0 <= x).
Proof. by rewrite !le0r invr_gt0 invr_eq0. Qed.

Lemma invr_lt0 x : (x^-1 < 0) = (x < 0).
Proof. by rewrite -oppr_cp0 -invrN invr_gt0 oppr_cp0. Qed.

Lemma invr_le0 x : (x^-1 <= 0) = (x <= 0).
Proof. by rewrite -oppr_cp0 -invrN invr_ge0 oppr_cp0. Qed.

Definition invr_gte0 := (invr_ge0, invr_gt0).
Definition invr_lte0 := (invr_le0, invr_lt0).

Lemma realV : {mono (@GRing.inv R) : x / x \in real}.
Proof. by move=> x /=; rewrite !realE invr_ge0 invr_le0. Qed.

(* ler and exprn *)
Lemma exprn_ge0 n x (hx : 0 <= x) : (0 <= x ^+ n).
Proof. by elim: n=> [|n ihn]; rewrite ?ler01 // exprS mulr_ge0 ?ihn. Qed.

Lemma realX n : {in real, forall x, x ^+ n \in real}.
Proof.
move=> x /orP [x_ge0|x_le0]; first by rewrite ger0_real ?exprn_ge0.
rewrite -[x]opprK -mulN1r exprMn realM -1?signr_odd //.
  by case: odd; rewrite (expr0, expr1) ?realN ?real1.
by rewrite ger0_real ?exprn_ge0 ?oppr_ge0.
Qed.

Lemma exprn_gt0 n x (hx : 0 < x) : (0 < x ^+ n).
Proof. by elim: n=> [|n ihn]; rewrite ?ltr01 // exprS pmulr_rgt0 ?ihn. Qed.

Definition exprn_gte0 := (exprn_ge0, exprn_gt0).

Lemma exprn_ile1 n x (x0 : 0 <= x) (x1 : x <= 1) : x ^+ n <= 1.
Proof. by elim: n=> [|*]; rewrite ?expr0 // exprS mulr_ile1 ?exprn_ge0. Qed.

Lemma exprn_ilt1 n x (x0 : 0 <= x) (x1 : x < 1) : x ^+ n < 1 = (n != 0%N).
Proof.
case: n; [by rewrite eqxx ltrr | elim=> [|n ihn]; first by rewrite expr1].
by rewrite exprS mulr_ilt1 // exprn_ge0.
Qed.

Definition exprn_ilte1 := (exprn_ile1, exprn_ilt1).

Lemma exprn_ege1 n x (x1 : 1 <= x) : 1 <= x ^+ n.
Proof. by elim: n=> [|n ihn]; rewrite ?expr0 // exprS mulr_ege1. Qed.

Lemma exprn_egt1 n x (x1 : 1 < x) : 1 < x ^+ n = (n != 0%N).
Proof.
case: n; [by rewrite eqxx ltrr | elim=> [|n ihn]; first by rewrite expr1].
by rewrite exprS mulr_egt1 // exprn_ge0.
Qed.

Definition exprn_egte1 := (exprn_ege1, exprn_egt1).
Definition exprn_cp1 := (exprn_ilte1, exprn_egte1).

Lemma ler_iexpr x n : (0 < n)%N -> 0 <= x -> x <= 1 -> x ^+ n <= x.
Proof. by case: n => n // *; rewrite exprS ler_pimulr // exprn_ile1. Qed.

Lemma ltr_iexpr x n : (0 < x) -> (x < 1) -> (x ^+ n < x) = (1 < n)%N.
Proof.
case: n=> [|[|n]] //; first by rewrite expr0 => _ /ltr_gtF ->.
by move=> x0 x1; rewrite exprS gtr_pmulr // ?exprn_ilt1 // ltrW.
Qed.

Definition lter_iexpr := (ler_iexpr, ltr_iexpr).

Lemma ler_eexpr x n : (0 < n)%N -> 1 <= x -> x <= x ^+ n.
Proof.
case: n => // n _ x_ge1.
by rewrite exprS ler_pemulr ?(ler_trans _ x_ge1) // exprn_ege1.
Qed.

Lemma ltr_eexpr x n (x_ge1 : 1 < x) : (x < x ^+ n) = (1 < n)%N.
Proof.
case: n=> [|[|n]] //; first by rewrite expr0 ltr_gtF.
by rewrite exprS ltr_pmulr ?(ltr_trans _ x_ge1) ?exprn_egt1.
Qed.

Definition lter_eexpr := (ler_eexpr, ltr_eexpr).
Definition lter_expr := (lter_iexpr, lter_eexpr).

Lemma ler_wiexpn2l x (x0 : 0 <= x) (x1 : x <= 1) :
  {homo (GRing.exp x) : m n / (n <= m)%N >-> m <= n}.
Proof.
move=> m n /= hmn.
by rewrite -(subnK hmn) exprD ler_pimull ?(exprn_ge0, exprn_ile1).
Qed.

Lemma ler_weexpn2l x (x1 : 1 <= x) :
  {homo (GRing.exp x) : m n / (m <= n)%N >-> m <= n}.
Proof.
move=> m n /= hmn; rewrite -(subnK hmn) exprD.
by rewrite ler_pemull ?(exprn_ge0, exprn_ege1) // (ler_trans _ x1) ?ler01.
Qed.

Lemma ieexprn_weq1 x n (x0 : 0 <= x) : (x ^+ n == 1) = ((n == 0%N) || (x == 1)).
Proof.
case: n => [|n]; first by rewrite expr0 eqxx.
case: (@real_ltrgtP x 1); do ?by rewrite ?ger0_real.
+ by move=> x_lt1; rewrite ?ltr_eqF // exprn_ilt1.
+ by move=> x_lt1; rewrite ?gtr_eqF // exprn_egt1.
by move->; rewrite expr1n eqxx.
Qed.

Lemma ieexprIn x (x0 : 0 < x) (nx1 : x != 1) : injective (GRing.exp x).
Proof.
apply: wlog_ltn=> // m n hmn; first by move=> hmn'; rewrite hmn.
move/eqP: hmn; rewrite exprD -{1}[x ^+ m]mulr1 eq_sym (inj_eq (mulfI _)).
  by rewrite ieexprn_weq1 ?ltrW //= (negPf nx1).
by rewrite expf_eq0 gtr_eqF // andbF.
Qed.

Lemma ler_iexpn2l x (x0 : 0 < x) (x1 : x < 1) :
  {mono (GRing.exp x) : m n / (n <= m)%N >-> m <= n}.
Proof.
apply: (nhomo_leq_mono (nhomo_inj_ltn_lt _ _)); last first.
  by apply: ler_wiexpn2l; rewrite ltrW.
by apply: ieexprIn; rewrite ?ltr_eqF ?ltr_cpable.
Qed.

Lemma ltr_iexpn2l x (x0 : 0 < x) (x1 : x < 1) :
  {mono (GRing.exp x) : m n / (n < m)%N >-> m < n}.
Proof. exact: (leq_lerW_nmono (ler_iexpn2l _ _)). Qed.

Definition lter_iexpn2l := (ler_iexpn2l, ltr_iexpn2l).

Lemma ler_eexpn2l x (x1 : 1 < x) :
  {mono (GRing.exp x) : m n / (m <= n)%N >-> m <= n}.
Proof.
apply: (homo_leq_mono (homo_inj_ltn_lt _ _)); last first.
  by apply: ler_weexpn2l; rewrite ltrW.
by apply: ieexprIn; rewrite ?gtr_eqF ?gtr_cpable //; apply: ltr_trans x1.
Qed.

Lemma ltr_eexpn2l x (x1 : 1 < x) :
  {mono (GRing.exp x) : m n / (m < n)%N >-> m < n}.
Proof. exact: (leq_lerW_mono (ler_eexpn2l _)). Qed.

Definition lter_eexpn2l := (ler_eexpn2l, ltr_eexpn2l).

Lemma ltr_expn2r n x y (x0 : 0 <= x) (xy : x < y) : x ^+ n < y ^+ n = (n != 0%N).
Proof.
case: n; [by rewrite ?ltrr | elim=> [|n ihn]; rewrite ?[_ ^+ _.+2]exprS //].
rewrite (@ler_lt_trans _ (x * y ^+ n.+1)) ?ler_wpmul2l ?ltr_pmul2r ?ihn //.
  by rewrite ltrW // ihn.
by rewrite exprn_gt0 // (ler_lt_trans x0).
Qed.

Lemma ler_expn2r n : {in >=%R 0 & , {homo ((@GRing.exp R)^~ n) : x y / x <= y}}.
Proof.
move=> x y /= x0 y0 xy; elim: n=> [|n ihn]; rewrite !(expr0, exprS) //.
by rewrite (@ler_trans _ (x * y ^+ n)) ?ler_wpmul2l ?ler_wpmul2r ?exprn_ge0.
Qed.

Definition lter_expn2r := (ler_expn2r, ltr_expn2r).

Lemma ltr_wpexpn2r n (hn : (0 < n)%N) :
  {in >=%R 0 & , {homo ((@GRing.exp R)^~ n) : x y / x < y}}.
Proof. by move=> x y /= x0 y0 hxy; rewrite ltr_expn2r // -lt0n. Qed.

Lemma ler_pexpn2r n : (0 <n)%N ->
  {in >=%R 0 & , {mono ((@GRing.exp R)^~ n) : x y / x <= y}}.
Proof.
case: n => // n _ x y; rewrite -!topredE /= =>  x_ge0 y_ge0.
have [-> | nzx] := eqVneq x 0; first by rewrite exprS mul0r exprn_ge0.
rewrite -subr_ge0 subrXX pmulr_lge0 ?subr_ge0 //= big_ord_recr /=.
rewrite subnn expr0 mul1r /= ltr_spaddr // ?exprn_gt0 ?lt0r ?nzx //.
by rewrite sumr_ge0 // => i _; rewrite mulr_ge0 ?exprn_ge0.
Qed.

Lemma ltr_pexpn2r n : (0 <n)%N ->
  {in >=%R 0 & , {mono ((@GRing.exp R)^~ n) : x y / x < y}}.
Proof.
by move=> n_gt0 x y x_ge0 y_ge0; rewrite !ltr_neqAle !eqr_le !ler_pexpn2r.
Qed.

Definition lter_pexpn2r := (ler_pexpn2r, ltr_pexpn2r).

Lemma pexpIrn n (hn : (0 < n)%N) : {in (>=%R 0) &, injective ((@GRing.exp R)^~ n)}.
Proof. exact: mono_inj_in (ler_pexpn2r _). Qed.


(* expr and ler/ltr *)
Lemma expr_le1 n x (n0 : (0 < n)%N) (x0 : 0 <= x) : (x ^+ n <= 1) = (x <= 1).
Proof. by rewrite -{1}[1](expr1n _ n) ler_pexpn2r // [_ \in _]ler01. Qed.

Lemma expr_lt1 n x (n0 : (0 < n)%N) (x0 : 0 <= x) : (x ^+ n < 1) = (x < 1).
Proof. by rewrite -{1}[1](expr1n _ n) ltr_pexpn2r // [_ \in _]ler01. Qed.

Definition expr_lte1 := (expr_le1, expr_lt1).

Lemma expr_ge1 n x (n0 : (0 < n)%N) (x0 : 0 <= x) : (1 <= x ^+ n) = (1 <= x).
Proof. by rewrite -{1}[1](expr1n _ n) ler_pexpn2r // [_ \in _]ler01. Qed.

Lemma expr_gt1 n x (n0 : (0 < n)%N) (x0 : 0 <= x) : (1 < x ^+ n) = (1 < x).
Proof. by rewrite -{1}[1](expr1n _ n) ltr_pexpn2r // [_ \in _]ler01. Qed.

Definition expr_gte1 := (expr_ge1, expr_gt1).

Lemma pexpr_eq1 x n (n0 : (0 < n)%N) (x0 : 0 <= x) : (x ^+ n == 1) = (x == 1).
Proof.
have [-> | nzx] := eqVneq x 0; first by rewrite expr0n gtn_eqF.
rewrite -subr_eq0 subrX1 mulf_eq0 subr_eq0.
case: (x == 1)=> //=; apply: negbTE.
rewrite psumr_eq0 /=; last by move=> i _; rewrite exprn_ge0.
case: n n0 => [//|n] _; apply/allPn; exists ord_max.
  by rewrite mem_index_enum.
by rewrite gtr_eqF // exprn_gt0 // lt0r nzx.
Qed.

Lemma pexprn_eq1 x n (x0 : 0 <= x) :
  (x ^+ n == 1) = ((n == 0%N) || (x == 1)).
Proof. by case: n => [|n]; rewrite ?eqxx // pexpr_eq1 ?gtn_eqF. Qed.

Lemma eqr_expn2 n x y : (0 < n)%N -> 0 <= x -> 0 <= y ->
  (x ^+ n == y ^+ n) = (x == y).
Proof. by  move=> *; rewrite (inj_in_eq (pexpIrn _)). Qed.

Lemma sqrp_eq1 x (hx : 0 <= x) : (x ^+ 2 == 1) = (x == 1).
Proof. by rewrite pexpr_eq1. Qed.

Lemma sqrn_eq1 x (hx : x <= 0) : (x ^+ 2 == 1) = (x == -1).
Proof. by rewrite -[_ ^+ 2]mulrNN sqrp_eq1 ?oppr_ge0 // eqr_oppC. Qed.

Lemma ler_pinv : {in [pred x | (x \in GRing.unit) && (0 < x)] &,
  {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof.
move=> x y /andP [ux hx] /andP [uy hy] /=.
rewrite -(ler_pmul2l hx) -(ler_pmul2r hy).
by rewrite !(divrr, mulrVK) ?unitf_gt0 // mul1r.
Qed.

Lemma ler_ninv : {in [pred x | (x \in GRing.unit) && (x < 0)] &,
  {mono (@GRing.inv R) : x y /~ x <= y}}.
Proof.
move=> x y /andP [ux hx] /andP [uy hy] /=.
rewrite -(ler_nmul2l hx) -(ler_nmul2r hy).
by rewrite !(divrr, mulrVK) ?unitf_lt0 // mul1r.
Qed.

Lemma ltr_pinv : {in [pred x | (x \in GRing.unit) && (0 < x)] &,
  {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. exact: lerW_nmono_in ler_pinv. Qed.

Lemma ltr_ninv : {in [pred x | (x \in GRing.unit) && (x < 0)] &,
  {mono (@GRing.inv R) : x y /~ x < y}}.
Proof. exact: lerW_nmono_in ler_ninv. Qed.

Lemma invr_gt1 x (ux : x \in GRing.unit) (hx : 0 < x) : (1 < x^-1) = (x < 1).
Proof. by rewrite -{1}[1]invr1 ltr_pinv ?inE ?unitr1 ?ltr01 // ux hx. Qed.

Lemma invr_ge1 x (ux : x \in GRing.unit) (hx : 0 < x) : (1 <= x^-1) = (x <= 1).
Proof. by rewrite -{1}[1]invr1 ler_pinv ?inE ?unitr1 ?ltr01 // ux hx. Qed.

Definition invr_gte1 := (invr_ge1, invr_gt1).

Lemma invr_le1 x (ux : x \in GRing.unit) (hx : 0 < x) : (x^-1 <= 1) = (1 <= x).
Proof. by rewrite -invr_ge1 ?invr_gt0 ?unitrV // invrK. Qed.

Lemma invr_lt1 x (ux : x \in GRing.unit) (hx : 0 < x) : (x^-1 < 1) = (1 < x).
Proof. by rewrite -invr_gt1 ?invr_gt0 ?unitrV // invrK. Qed.

Definition invr_lte1 := (invr_le1, invr_lt1).
Definition invr_cp1 := (invr_gte1, invr_lte1).

(* norm + add *)

Lemma normr_real x : `|x| \in real. Proof. by rewrite ger0_real. Qed.
Hint Resolve normr_real.

Lemma ler_norm_sum I r (G : I -> R) (P : pred I):
  `|\sum_(i <- r | P i) G i| <= \sum_(i <- r | P i) `|G i|.
Proof.
apply: (big_ind2 (fun a b => `| a | <= b)); rewrite // ?normr0 //.
by move=> *; rewrite (ler_trans (ler_norm_add _ _)) // ler_add.
Qed.

Lemma ler_norm_sub x y : `|x - y| <= `|x| + `|y|.
Proof. by rewrite (ler_trans (ler_norm_add _ _)) ?normrN. Qed.

Lemma ler_dist_add (z x y : R) :  `|x - y| <= `| x - z | + `| z - y |.
Proof. by rewrite (ler_trans _ (ler_norm_add _ _)) // addrA addrNK. Qed.

Lemma ler_sub_norm_add x y : `|x| - `|y| <= `| x + y |.
Proof.
rewrite -{1}[x](addrK y) lter_sub_addl.
by rewrite (ler_trans (ler_norm_add _ _)) // addrC normrN.
Qed.

Lemma ler_sub_dist x y : `|x| - `|y| <= `|x - y|.
Proof. by rewrite -[`|y|]normrN ler_sub_norm_add. Qed.

Lemma ler_dist_dist x y : `|`|x| - `|y| | <= `|x - y|.
Proof.
have [||_|_] // := @real_lerP `|x| `|y|; last by rewrite ler_sub_dist.
by rewrite distrC ler_sub_dist.
Qed.

Lemma ler_dist_norm_add x y : `| `|x| - `|y| | <= `| x + y |.
Proof. by rewrite -[y]opprK normrN ler_dist_dist. Qed.

Lemma real_ler_norml x y : x \in real -> (`|x| <= y) = (- y <= x <= y).
Proof.
move=> xR; wlog x_ge0 : x xR / 0 <= x => [hwlog|].
  move: (xR) => /(@real_leVge 0) /orP [|/hwlog->|hx] //.
  by rewrite -[x]opprK normrN ler_opp2 andbC ler_oppl hwlog ?realN ?oppr_ge0.
rewrite ger0_norm //; have [le_xy|] := boolP (x <= y); last by rewrite andbF.
by rewrite (ler_trans _ x_ge0) // oppr_le0 (ler_trans x_ge0).
Qed.

Lemma real_ler_normlP x y (xR : x \in real) :
  reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Proof.
by rewrite real_ler_norml // ler_oppl; apply: (iffP (@andP _ _)); case.
Qed.
Implicit Arguments real_ler_normlP [x y xR].

Lemma real_eqr_norml x y (xR : x \in real) :
  (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof.
apply/idP/idP=> [|/andP [/orP [] /eqP-> /ger0_norm /eqP]]; rewrite ?normrE //.
case: real_ler0P => // hx; rewrite 1?eqr_oppC => /eqP exy.
  by move: hx; rewrite exy ?oppr_le0 eqxx orbT //.
by move: hx=> /ltrW; rewrite exy eqxx.
Qed.

Lemma real_eqr_norm2 x y (xR : x \in real) (yR : y \in real) :
  (`|x| == `|y|) = (x == y) || (x == -y).
Proof.
rewrite real_eqr_norml // normrE andbT.
by case: real_ler0P; rewrite // opprK orbC.
Qed.

Lemma real_ltr_norml x y (xR : x \in real) : (`|x| < y) = (- y < x < y).
Proof.
wlog x_ge0 : x xR / 0 <= x => [hwlog|].
  move: (xR) => /(@real_leVge 0) /orP [|/hwlog->|hx] //.
  by rewrite -[x]opprK normrN ltr_opp2 andbC ltr_oppl hwlog ?realN ?oppr_ge0.
rewrite ger0_norm //; have [le_xy|] := boolP (x < y); last by rewrite andbF.
by rewrite (ltr_le_trans _ x_ge0) // oppr_lt0 (ler_lt_trans x_ge0).
Qed.

Definition real_lter_norml := (real_ler_norml, real_ltr_norml).

Lemma real_ltr_normlP x y (xR : x \in real) :
  reflect ((-x < y) * (x < y)) (`|x| < y).
Proof.
by rewrite real_ltr_norml // ltr_oppl; apply: (iffP (@andP _ _)); case.
Qed.
Implicit Arguments real_ltr_normlP [x y xR].

Lemma real_ler_normr x y (yR : y \in real) :
  (x <= `|y|) = (x <= y) || (x <= - y).
Proof.
have [xR|xNR] := boolP (x \in real); last by rewrite ?Nreal_leF ?realN.
rewrite real_lerNgt ?real_ltr_norml // negb_and -?real_lerNgt ?realN //.
by rewrite orbC ler_oppr.
Qed.

Lemma real_ltr_normr x y (yR : y \in real) :
  (x < `|y|) = (x < y) || (x < - y).
Proof.
have [xR|xNR] := boolP (x \in real); last by rewrite ?Nreal_ltF ?realN.
rewrite real_ltrNge ?real_ler_norml // negb_and -?real_ltrNge ?realN //.
by rewrite orbC ltr_oppr.
Qed.

Definition real_lter_normr :=  (real_ler_normr, real_ltr_normr).

Lemma ler_nnorml x y (hy : y < 0) : (`|x| <= y = false).
Proof. by rewrite ltr_geF // (ltr_le_trans hy). Qed.

Lemma ltr_nnorml x y (hy : y <= 0) : (`|x| < y = false).
Proof. by rewrite ler_gtF // (ler_trans hy). Qed.

Definition lter_nnormr := (ler_nnorml, ltr_nnorml).

Lemma real_ler_distl x y e (xyR : x - y \in real) :
  (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. by rewrite real_lter_norml // !lter_sub_addl. Qed.

Lemma real_ltr_distl x y e (xyR : x - y \in real) :
  (`|x - y| < e) = (y - e < x < y + e).
Proof. by rewrite real_lter_norml // !lter_sub_addl. Qed.

Definition real_lter_distl := (real_ler_distl, real_ltr_distl).

Lemma ler0_def x : (x <= 0) = (`|x| == - x).
Proof. by rewrite -{2}[x]opprK normrN -ger0_def oppr_ge0. Qed.

Lemma eqr_norm_id x : (`|x| == x) = (0 <= x). Proof. by rewrite ger0_def. Qed.
Lemma eqr_normN x : (`|x| == -x) = (x <= 0). Proof. by rewrite ler0_def. Qed.
Definition eqr_norm_idVN := (eqr_norm_id, eqr_normN).

Lemma real_exprn_even_ge0 n x : x \in real -> ~~ odd n -> 0 <= x ^+ n.
Proof.
move=> xR even_n; have [/exprn_ge0 -> //|x_lt0] := real_ger0P xR.
rewrite -[x]opprK -mulN1r exprMn -signr_odd (negPf even_n) expr0 mul1r.
by rewrite exprn_ge0 ?oppr_ge0 ?ltrW.
Qed.

(* particular case for squares *)
Lemma real_sqr_ge0 (x : R) : x \in real -> 0 <= x ^+ 2.
Proof. by move=> xR; rewrite real_exprn_even_ge0. Qed.

(* norm    and    unit & inv *)

Lemma normr_unit : {homo (@normr R) : x / x \in GRing.unit}.
Proof.
move=> x /= /unitrP [y [yx xy]]; apply/unitrP; exists `|y|.
by rewrite -!normrM xy yx normr1.
Qed.

Lemma normrV : {in GRing.unit, {morph (@normr R) : x / x ^-1}}.
Proof.
move=> x ux; apply: (mulrI (normr_unit ux)).
by rewrite -normrM !divrr ?normr1 ?normr_unit.
Qed.

(* sign *)

Lemma normr_sign (s : nat) : `|(-1) ^+ s| = 1 :> R.
Proof. by rewrite normrX normrN1 expr1n. Qed.

Lemma sgr_def (x : R) : sg x = (-1) ^+ (x < 0)%R *+ (x != 0).
Proof. by rewrite /sg; case: (_ == _); case: (_ < _). Qed.

Lemma signr_gt0 (b : bool) : (0 < (-1) ^+ b :> R) = ~~ b.
Proof. by case: b; rewrite (ltr01, ltr0N1). Qed.

Lemma signr_lt0 (b : bool) : ((-1) ^+ b < 0 :> R) = b.
Proof. by case: b; rewrite // ?(ltrN10, ltr10). Qed.

Lemma signr_ge0 (b : bool) : (0 <= (-1) ^+ b :> R) = ~~ b.
Proof. by rewrite le0r signr_eq0 signr_gt0. Qed.

Lemma signr_le0 (b : bool) : ((-1) ^+ b <= 0 :> R) = b.
Proof. by rewrite ler_eqVlt signr_eq0 signr_lt0. Qed.

Lemma neqr0_sign (x : R) : x != 0 -> (-1) ^+ (x < 0)%R = sgr x.
Proof. by rewrite sgr_def  => ->. Qed.

End PIntegralDomainOperationTheory.

Section PIntegralDomainMonotonyTheoryBis.

Variables R R' : PIntegralDomain.type.
Implicit Types m n p : nat.
Implicit Types x y z : R.
Implicit Types u v w : R'.

Variable D : pred R.
Variable (f : R -> R').

Lemma real_mono (mf : {homo f : x y / x < y}) :
  {in real &, {mono f : x y / x <= y}}.
Proof.
move=> x y xR yR /=; have [lt_xy|le_yx] := real_lerP xR yR.
  by rewrite ltrW_homo.
by rewrite ltr_geF ?mf.
Qed.

Lemma real_nmono (mf : {homo f : x y /~ x < y}) :
  {in real &, {mono f : x y /~ x <= y}}.
Proof.
move=> x y xR yR /=; have [lt_xy|le_yx] := real_ltrP xR yR.
  by rewrite ltr_geF ?mf.
by rewrite ltrW_nhomo.
Qed.

Lemma real_mono_in (mf : {in D &, {homo f : x y / x < y}}) :
  {in [pred x | (x \in real) && (x \in D)] &, {mono f : x y / x <= y}}.
Proof.
move=> x y /andP [xR hx] /andP [yR hy] /=.
have [lt_xy|le_yx] := real_lerP xR yR.
  by rewrite (ltrW_homo_in mf).
by rewrite ltr_geF ?mf.
Qed.

Lemma real_nmono_in  (mf : {in D &, {homo f : x y /~ x < y}}) :
  {in [pred x | (x \in real) && (x \in D)] &, {mono f : x y /~ x <= y}}.
Proof.
move=> x y /andP [xR hx] /andP [yR hy] /=.
have [lt_xy|le_yx] := real_ltrP xR yR.
  by rewrite ltr_geF ?mf.
by rewrite (ltrW_nhomo_in mf).
Qed.

End PIntegralDomainMonotonyTheoryBis.

End PIntegralDomainTheory.

Module PField.

Include PIntegralDomainTheory.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.Field.class_of R; mixin : ring_mixin_of R base }.
Definition base2 R (c : class_of R) := PIntegralDomain.Class (mixin c).
Local Coercion base : class_of >-> GRing.Field.class_of.
Local Coercion base2 : class_of >-> PIntegralDomain.class_of.

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
Definition poIdomainType cT := PIntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition join_poIdomainType cT :=
  @PIntegralDomain.Pack (fieldType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.Field.class_of.
Coercion base2 : class_of >-> PIntegralDomain.class_of.
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
Coercion poIdomainType : type >-> PIntegralDomain.type.
Canonical poIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.

End Exports.

End PField.
Import PField.Exports.

Module PFieldTheory.
Import PIntegralDomainTheory.

Section PFieldTheory.

Hint Resolve lerr.

Variable F : PField.type.
Implicit Types x y z t : F.

Lemma unitf_gt0 x : 0 < x -> x \in GRing.unit.
Proof. by move=> hx; rewrite unitfE eq_sym ltr_eqF. Qed.

Lemma unitf_lt0 x : x < 0 -> x \in GRing.unit.
Proof. by move=> hx; rewrite unitfE ltr_eqF. Qed.

Lemma lef_pinv : {in >%R 0 &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. by move=> x y hx hy /=; rewrite ler_pinv ?inE ?unitf_gt0. Qed.

Lemma lef_ninv : {in <%R 0 &, {mono (@GRing.inv F) : x y /~ x <= y}}.
Proof. by move=> x y hx hy /=; rewrite ler_ninv ?inE ?unitf_lt0. Qed.

Lemma ltf_pinv : {in >%R 0 &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. exact: lerW_nmono_in lef_pinv. Qed.

Lemma ltf_ninv: {in <%R 0 &, {mono (@GRing.inv F) : x y /~ x < y}}.
Proof. exact: lerW_nmono_in lef_ninv. Qed.

Definition ltef_pinv := (lef_pinv, ltf_pinv).
Definition ltef_ninv := (lef_ninv, ltf_ninv).

Lemma invf_gt1 x (hx : 0 < x) : (1 < x^-1) = (x < 1).
Proof. by rewrite -{1}[1]invr1 ltf_pinv -?topredE /= ?ltr01. Qed.

Lemma invf_ge1 x (hx : 0 < x) : (1 <= x^-1) = (x <= 1).
Proof. by rewrite -{1}[1]invr1 lef_pinv -?topredE /= ?ltr01. Qed.

Definition invf_gte1 := (invf_ge1, invf_gt1).

Lemma invf_le1 x (hx : 0 < x) : (x^-1 <= 1) = (1 <= x).
Proof. by rewrite -invf_ge1 ?invr_gt0 // invrK. Qed.

Lemma invf_lt1 x (hx : 0 < x) : (x^-1 < 1) = (1 < x).
Proof. by rewrite -invf_gt1 ?invr_gt0 // invrK. Qed.

Definition invf_lte1 := (invf_le1, invf_lt1).
Definition invf_cp1 := (invf_gte1, invf_lte1).

(* all those lemma are a combination of mono(LR|RL) with ler_[pn]mul2[rl] *)
Lemma ler_pdivl_mulr z x y (hz : 0 < z) : (x <= y / z) = (x * z <= y).
Proof. by rewrite -(@ler_pmul2r _ z) ?mulfVK ?gtr_eqF. Qed.

Lemma ltr_pdivl_mulr z x y (hz : 0 < z) : (x < y / z) = (x * z < y).
Proof. by rewrite -(@ltr_pmul2r _ z) ?mulfVK ?gtr_eqF. Qed.

Definition lter_pdivl_mulr := (ler_pdivl_mulr, ltr_pdivl_mulr).

Lemma ler_pdivr_mulr z x y (hz : 0 < z) : (y / z <= x) = (y <= x * z).
Proof. by rewrite -(@ler_pmul2r _ z) ?mulfVK ?gtr_eqF. Qed.

Lemma ltr_pdivr_mulr z x y (hz : 0 < z) : (y / z < x) = (y < x * z).
Proof. by rewrite -(@ltr_pmul2r _ z) ?mulfVK ?gtr_eqF. Qed.

Definition lter_pdivr_mulr := (ler_pdivr_mulr, ltr_pdivr_mulr).

Lemma ler_pdivl_mull z x y (hz : 0 < z) : (x <= z^-1 * y) = (z * x <= y).
Proof. by rewrite mulrC ler_pdivl_mulr ?[z * _]mulrC. Qed.

Lemma ltr_pdivl_mull z x y (hz : 0 < z) : (x < z^-1 * y) = (z * x < y).
Proof. by rewrite mulrC ltr_pdivl_mulr ?[z * _]mulrC. Qed.

Definition lter_pdivl_mull := (ler_pdivl_mull, ltr_pdivl_mull).

Lemma ler_pdivr_mull z x y (hz : 0 < z) : (z^-1 * y <= x) = (y <= z * x).
Proof. by rewrite mulrC ler_pdivr_mulr ?[z * _]mulrC. Qed.

Lemma ltr_pdivr_mull z x y (hz : 0 < z) : (z^-1 * y < x) = (y < z * x).
Proof. by rewrite mulrC ltr_pdivr_mulr ?[z * _]mulrC. Qed.

Definition lter_pdivr_mull := (ler_pdivr_mull, ltr_pdivr_mull).

Lemma ler_ndivl_mulr z x y (hz : z < 0) : (x <= y / z) = (y <= x * z).
Proof. by rewrite -(@ler_nmul2r _ z) ?mulfVK  ?ltr_eqF. Qed.

Lemma ltr_ndivl_mulr z x y (hz : z < 0) : (x < y / z) = (y < x * z).
Proof. by rewrite -(@ltr_nmul2r _ z) ?mulfVK ?ltr_eqF. Qed.

Definition lter_ndivl_mulr := (ler_ndivl_mulr, ltr_ndivl_mulr).

Lemma ler_ndivr_mulr z x y (hz : z < 0) : (y / z <= x) = (x * z <= y).
Proof. by rewrite -(@ler_nmul2r _ z) ?mulfVK ?ltr_eqF. Qed.

Lemma ltr_ndivr_mulr z x y (hz : z < 0) : (y / z < x) = (x * z < y).
Proof. by rewrite -(@ltr_nmul2r _ z) ?mulfVK ?ltr_eqF. Qed.

Definition lter_ndivr_mulr := (ler_ndivr_mulr, ltr_ndivr_mulr).

Lemma ler_ndivl_mull z x y (hz : z < 0) : (x <= z^-1 * y) = (y <= z * x).
Proof. by rewrite mulrC ler_ndivl_mulr ?[z * _]mulrC. Qed.

Lemma ltr_ndivl_mull z x y (hz : z < 0) : (x < z^-1 * y) = (y < z * x).
Proof. by rewrite mulrC ltr_ndivl_mulr ?[z * _]mulrC. Qed.

Definition lter_ndivl_mull := (ler_ndivl_mull, ltr_ndivl_mull).

Lemma ler_ndivr_mull z x y (hz : z < 0) : (z^-1 * y <= x) = (z * x <= y).
Proof. by rewrite mulrC ler_ndivr_mulr ?[z * _]mulrC. Qed.

Lemma ltr_ndivr_mull z x y (hz : z < 0) : (z^-1 * y < x) = (z * x < y).
Proof. by rewrite mulrC ltr_ndivr_mulr ?[z * _]mulrC. Qed.

Definition lter_ndivr_mull := (ler_ndivr_mull, ltr_ndivr_mull).

Lemma normfV : {morph (@normr F) : x / x ^-1}.
Proof.
move=> x /=; have [/normrV //|Nux] := boolP (GRing.unit x).
by rewrite !invr_out // unitfE normr_eq0 -unitfE.
Qed.

End PFieldTheory.
End PFieldTheory.

Module ClosedField.

Section ClassDef.

Record class_of R :=
  Class { base : GRing.ClosedField.class_of R; mixin : ring_mixin_of R base }.
Definition base2 R (c : class_of R) := PField.Class (mixin c).
Local Coercion base : class_of >-> GRing.ClosedField.class_of.
Local Coercion base2 : class_of >-> PField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack Pack Class GRing.ClosedField.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := PIntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition decFieldType cT := GRing.DecidableField.Pack (class cT) cT.
Definition closedFieldType cT := GRing.ClosedField.Pack (class cT) cT.
Definition join_poIdomainType cT :=
  @PIntegralDomain.Pack (closedFieldType cT) (class cT) cT.
Definition join_poFieldType cT :=
  @PField.Pack (closedFieldType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> GRing.ClosedField.class_of.
Coercion base2 : class_of >-> PField.class_of.
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
Coercion poIdomainType : type >-> PIntegralDomain.type.
Canonical poIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion decFieldType : type >-> GRing.DecidableField.type.
Canonical decFieldType.
Coercion closedFieldType : type >-> GRing.ClosedField.type.
Canonical closedFieldType.

End Exports.

End ClosedField.
Import ClosedField.Exports.

Definition total_mixin_of (R : PIntegralDomain.type) :=
  forall x : R, x \in real.

Section POLeMixin.

Variable R : GRing.IntegralDomain.type.
Variable le : rel R.
Variable lt : rel R.
Variable norm : R -> R.
Hypothesis le0_add : forall x y, le 0 x -> le 0 y -> le 0 (x + y).
Hypothesis le0_mul : forall x y, le 0 x -> le 0 y -> le 0 (x * y).
Hypothesis le0_anti : forall x,  le 0 x -> le x 0 -> x = 0.
Hypothesis sub_ge0  : forall x y, le 0 (y - x) = le x y.
Hypothesis le0_total : forall x, le 0 x || le x 0.
Hypothesis normN: forall x, norm (- x) = norm x.
Hypothesis ge0_norm : forall x, le 0 x -> norm x = x.
Hypothesis lt_def : forall x y, (lt x y) = (y != x) && (le x y).

Fact le0N x : le 0 (-x) = le x 0.
Proof. by rewrite -[RHS]sub_ge0 sub0r. Qed.

Fact lt0N x : lt 0 (-x) = lt x 0.
Proof. by rewrite !lt_def oppr_eq0 le0N eq_sym. Qed.

Fact le00 : le 0 0. Proof. by have := le0_total 0; rewrite orbb. Qed.

Fact le01 : le 0 1.
Proof.
by case/orP: (le0_total 1)=> // ?; rewrite -[1]mul1r -mulrNN le0_mul ?le0N.
Qed.

Fact lt0_add x y : lt 0 x -> lt 0 y -> lt 0 (x + y).
Proof.
rewrite !lt_def => /andP [x_neq0 l0x] /andP [y_neq0 l0y]; rewrite le0_add //.
rewrite andbT; apply: contra x_neq0; rewrite addr_eq0 => /eqP hxy.
by apply/eqP/le0_anti; rewrite // hxy -le0N opprK.
Qed.

Fact lt_eqF x y : lt x y -> x == y = false.
Proof. by rewrite lt_def eq_sym => /andP [/negPf]. Qed.

Fact eq0_norm x : norm x = 0 -> x = 0.
Proof.
have /orP [x_ge0|x_le0 /eqP] := le0_total x; first by rewrite ge0_norm.
by rewrite -normN ge0_norm ?le0N // oppr_eq0 => /eqP.
Qed.

Fact le_def : forall x y, (le x y) = (norm (y - x) == y - x).
Proof.
suff le0_def: forall x, le 0 x = (norm x == x).
  by move=> x y; rewrite -sub_ge0 le0_def.
move=> x; have /orP [x_ge0|x_le0] := le0_total x.
  by rewrite ge0_norm ?hxy ?eqxx.
rewrite -normN ge0_norm ?le0N // eq_sym -addr_eq0.
have [->|x_neq0] := eqVneq x 0; first by rewrite le00 addr0 eqxx.
rewrite lt_eqF; first by apply: contraNF x_neq0 => /le0_anti ->.
by rewrite -lt0N opprD lt0_add ?lt0N // lt_def eq_sym x_neq0.
Qed.

Fact normM : {morph norm : x y / x * y}.
Proof.
move=> x y /=; wlog x_ge0 : x / le 0 x => [hwlog|].
  have /orP [/hwlog //|x_le0] := le0_total x.
  by rewrite -normN -mulNr hwlog ?le0N // normN.
have /orP [y_ge0|y_le0] := le0_total y; first by rewrite ?ge0_norm ?le0_mul.
by rewrite -normN -mulrN -[norm y]normN ?ge0_norm ?le0_mul ?le0N.
Qed.

Fact le_normD x y : le (norm (x + y)) (norm x + norm y).
Proof.
wlog x_ge0 : x y / le 0 x => [hwlog|].
  have /orP [/hwlog //|x_le0] := le0_total x.
  by rewrite -normN opprD -[norm x]normN -[norm y]normN hwlog ?le0N.
rewrite [norm x]ge0_norm //; have /orP [y_ge0|y_le0] := le0_total y.
  by rewrite ?ge0_norm ?le0_add // -sub_ge0 subrr le00.
rewrite -[norm y]normN [norm (- y)]ge0_norm ?le0N // -sub_ge0.
have /orP [hxy|hxy] := le0_total (x + y).
  by rewrite ge0_norm // opprD addrCA -addrA addKr le0_add ?le0N.
by rewrite -normN ge0_norm ?le0N // opprK addrCA addrNK le0_add.
Qed.

Lemma le_total x y : le x y || le y x.
Proof. by rewrite -sub_ge0 -opprB le0N orbC -sub_ge0 le0_total. Qed.

Definition TotalPLeMixin := Mixin le_normD lt0_add eq0_norm
              (fun x y _ _ => le_total x y) normM le_def lt_def.

End POLeMixin.


Section POLtMixin.

Variable R : GRing.IntegralDomain.type.
Variable le : rel R.
Variable lt : rel R.
Variable norm : R -> R.
Hypothesis lt0_add : forall x y, lt 0 x -> lt 0 y -> lt 0 (x + y).
Hypothesis lt0_mul : forall x y, lt 0 x -> lt 0 y -> lt 0 (x * y).
Hypothesis lt0_ngt0  : forall x,  lt 0 x -> ~~ lt x 0.
Hypothesis sub_gt0  : forall x y, lt 0 (y - x) = lt x y.
Hypothesis lt0_total : forall x, x != 0 -> lt 0 x || lt x 0.
Hypothesis normN : forall x, norm (- x) = norm x.
Hypothesis ge0_norm : forall x, le 0 x -> norm x = x.
Hypothesis le_def : forall x y, (le x y) = (y == x) || (lt x y).

Fact le0_add x y : le 0 x -> le 0 y -> le 0 (x + y).
Proof.
rewrite !le_def => /orP[/eqP->|x_gt0] /orP[/eqP->|y_gt0];
  do ?by rewrite ?(addr0, add0r) ?eqxx ?x_gt0 ?y_gt0 // ?orbT.
by rewrite lt0_add ?orbT.
Qed.

Fact le0_mul x y : le 0 x -> le 0 y -> le 0 (x * y).
Proof.
rewrite !le_def => /orP[/eqP->|x_gt0] /orP[/eqP->|y_gt0];
by rewrite ?(mulr0, mul0r, eqxx) // lt0_mul ?orbT.
Qed.

Fact le0_anti x :  le 0 x -> le x 0 -> x = 0.
Proof.
rewrite !le_def => /orP[/eqP->|x_gt0] /orP[/eqP->|] //.
by rewrite -[lt _ _]negbK lt0_ngt0.
Qed.

Fact sub_ge0  x y : le 0 (y - x) = le x y.
Proof. by rewrite !le_def subr_eq0 sub_gt0. Qed.

Fact lt_def x y : (lt x y) = (y != x) && (le x y).
Proof.
rewrite !le_def; case: (altP eqP) => //= ->; rewrite -sub_gt0 subrr.
by have /implyP := (@lt0_ngt0 0); case: lt.
Qed.

Lemma TLtMixin x : le 0 x || le x 0.
Proof.
by rewrite !le_def [0 == _]eq_sym; have [//|/lt0_total] := altP eqP.
Qed.

Definition TotalPLtMixin := TotalPLeMixin le0_add le0_mul le0_anti sub_ge0
  TLtMixin normN ge0_norm lt_def.

End POLtMixin.

Local Notation oidom_mixin_of T b :=
  (total_mixin_of (@PIntegralDomain.Pack T b T)).

Section Generic'.

(* Implicits *)
Variables (BFtype base_type : Type) (BFclass_of base_of : Type -> Type).
Variable to_oidom : forall T, base_of T -> PIntegralDomain.class_of T.
Variable base_sort : base_type -> Type.

(* Explicits *)
Variable Pack : forall T, BFclass_of T -> Type -> BFtype.
Variable Class : forall T b, oidom_mixin_of T (to_oidom b) -> BFclass_of T.
Variable base_class : forall bT, base_of (base_sort bT).

Definition gen_pack' T b0 (m0 : oidom_mixin_of T b0) :=
  fun bT b & phant_id (base_class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

End Generic'.

Implicit Arguments
   gen_pack' [BFtype base_type BFclass_of base_of to_oidom base_sort].

Module TIntegralDomain.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : PIntegralDomain.class_of R;
  mixin : total_mixin_of (PIntegralDomain.Pack base R)
}.
Local Coercion base : class_of >-> PIntegralDomain.class_of.
Local Coercion mixin : class_of >-> total_mixin_of.
Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack' Pack Class PIntegralDomain.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poidomainType cT := PIntegralDomain.Pack (class cT) cT.
Definition join_idomainType cT :=
  @GRing.IntegralDomain.Pack (poidomainType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PIntegralDomain.class_of.
Coercion mixin : class_of >-> total_mixin_of.
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
Coercion poidomainType : type >-> PIntegralDomain.type.
Canonical poidomainType.
End Exports.

End TIntegralDomain.
Import TIntegralDomain.Exports.

Module TIntegralDomainTheory.
Import PIntegralDomainTheory.

Section TIntegralDomainTheory.

Hint Resolve lerr.

Variable R : TIntegralDomain.type.
Implicit Types x y z t : R.

Lemma ordered_real x : x \in real. Proof. by case: R x=> T []. Qed.
Hint Resolve ordered_real.

Lemma ler_total : total (@ler R). Proof. by move=> *; apply: real_leVge. Qed.

Lemma ltr_total x y : x != y -> (x < y) || (y < x).
Proof. by rewrite !ltr_def [_ == y]eq_sym=> ->; apply: ler_total. Qed.

Lemma wlog_ler P : (forall a b, P b a -> P a b)
  -> (forall a b, a <= b -> P a b) -> forall a b : R, P a b.
Proof. by move=> sP hP a b; apply: real_wlog_ler. Qed.

Lemma wlog_ltr P : (forall a, P a a) -> (forall a b, (P b a -> P a b))
  -> (forall a b, a < b -> P a b) -> forall a b : R, P a b.
Proof. by move=> rP sP hP a b; apply: real_wlog_ltr. Qed.

Lemma ltrNge x y : (x < y) = ~~ (y <= x). Proof. by rewrite real_ltrNge. Qed.

Lemma lerNgt x y : (x <= y) = ~~ (y < x). Proof. by rewrite real_lerNgt. Qed.

Lemma lerP x y : ler_xor_gt x y `|x - y| `|y - x| (x <= y) (y < x).
Proof. by case: real_lerP=> // *; constructor. Qed.

Lemma ltrP x y : ltr_xor_ge x y `|x - y| `|y - x| (y <= x) (x < y).
Proof. by case: real_ltrP=> // *; constructor. Qed.

Lemma ltrgtP x y : cparer x y `|x - y| `|y - x| (y == x) (x == y)
  (x <= y) (y <= x) (x < y) (x > y) .
Proof. by case: real_ltrgtP=> // *; constructor. Qed.

Lemma ger0P x : ger0_xor_lt0 x `|x| (x < 0) (0 <= x).
Proof. by case: real_ger0P=> //; constructor. Qed.

Lemma ler0P x : ler0_xor_gt0 x `|x| (0 < x) (x <= 0).
Proof. by case: real_ler0P=> //; constructor. Qed.

Lemma ltrgt0P x :
  cparer0 x `|x| (0 == x) (x == 0) (x <= 0) (0 <= x) (x < 0) (x > 0).
Proof. by case: real_ltrgt0P=> //; constructor. Qed.

Lemma neqr_lt x y : (x != y) = (x < y) || (y < x).
Proof. exact: real_neqr_lt. Qed.

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

(* sign *)

Lemma mulr_sign_norm (x : R) : (-1) ^+ (x < 0)%R * `|x| = x.
Proof. by case: ger0P; rewrite (mul1r, mulN1r) ?opprK. Qed.

Lemma mulr_Nsign_norm (x : R) :
  (-1) ^+ (0 < x)%R * `|x| = - x.
Proof. by rewrite -normrN -oppr_lt0 mulr_sign_norm. Qed.

Lemma normr_dec_sign (x : R) : `|x| = (-1) ^+ (x < 0)%R * x.
Proof. by rewrite -{3}[x]mulr_sign_norm mulrA -signr_addb addbb mul1r. Qed.

Lemma neq0_mulr_lt0 (x y : R) : x != 0 -> y != 0 ->
         (x * y < 0) = (x < 0) (+) (y < 0).
Proof.
move=> x_neq0 y_neq0; case: (ltrgt0P x) x_neq0 => //= hx _.
  by rewrite pmulr_rlt0.
by rewrite nmulr_rlt0 //; case: ltrgt0P y_neq0.
Qed.

Section FinGroup.

Import GroupScope.

Variable gT : finGroupType.
Implicit Types G H : {group gT}.

Lemma natrG_gt0 G : #|G|%:R > 0 :> R.
Proof. by rewrite ltr0n cardG_gt0. Qed.

Lemma natrG_neq0 G : #|G|%:R != 0 :> R.
Proof. by rewrite gtr_eqF // natrG_gt0. Qed.

Lemma natr_indexg_gt0 G H : #|G : H|%:R > 0 :> R.
Proof. by rewrite ltr0n indexg_gt0. Qed.

Lemma natr_indexg_neq0 G H : #|G : H|%:R != 0 :> R.
Proof. by rewrite gtr_eqF // natr_indexg_gt0. Qed.

End FinGroup.

End TIntegralDomainTheory.

Hint Resolve ordered_real.

Section TIntegralDomainMonotonyTheory.

Variables R R' : TIntegralDomain.type.
Implicit Types m n p : nat.
Implicit Types x y z : R.
Implicit Types u v w : R'.

Variable D : pred R.
Variable (f : R -> R').

Lemma homo_mono (mf : {homo f : x y / x < y}) : {mono f : x y / x <= y}.
Proof. by move=> *; apply: real_mono; rewrite ?ordered_real. Qed.

Lemma nhomo_mono (mf : {homo f : x y /~ x < y}) : {mono f : x y /~ x <= y}.
Proof. by move=> *; apply: real_nmono; rewrite ?ordered_real. Qed.

Lemma homo_mono_in (mf : {in D &, {homo f : x y / x < y}}) :
  {in D &, {mono f : x y / x <= y}}.
Proof.
by move=> *; apply: (real_mono_in mf); rewrite ?inE ?ordered_real.
Qed.

Lemma nhomo_mono_in (mf : {in D &, {homo f : x y /~ x < y}}) :
  {in D &, {mono f : x y /~ x <= y}}.
Proof.
by move=> *; apply: (real_nmono_in mf); rewrite ?inE ?ordered_real.
Qed.

End TIntegralDomainMonotonyTheory.

Section TIntegralDomainOperationTheory.
(* sgr section *)

Hint Resolve lerr.
Hint Resolve ordered_real.

Variable R : TIntegralDomain.type.
Implicit Types x y z t : R.

Lemma sgr_cp0 x :
  ((sgr x == 1) = (0 < x)) *
  ((sgr x == -1) = (x < 0)) *
  ((sgr x == 0) = (x == 0)).
Proof.
rewrite /sgr; case: ltrgtP=> // hx; rewrite ?eqxx; do !split => //;
rewrite -subr_eq0 ?opprK ?add0r ?subr0 -?opprD ?oppr_eq0 -?mulr2n;
by rewrite (oner_eq0, pnatr_eq0).
Qed.

Lemma gtr0_sg x : 0 < x -> sgr x = 1.
Proof. by move=> hx; apply/eqP; rewrite sgr_cp0. Qed.

Lemma ltr0_sg x : x < 0 -> sgr x = -1.
Proof. by move=> hx; apply/eqP; rewrite sgr_cp0. Qed.

Lemma sgr0 : sgr (0 : R) = 0. Proof. by rewrite /sgr eqxx. Qed.
Lemma sgr1 : sgr (1 : R) = 1. Proof. by rewrite gtr0_sg // ltr01. Qed.
Lemma sgrN1 : sgr (-1 : R) = -1. Proof. by rewrite ltr0_sg // ltrN10. Qed.

Definition sgrE := (sgr0, sgr1, sgrN1).

CoInductive sgr_val x : R -> bool -> bool -> bool -> bool -> bool -> bool
  -> bool -> bool -> bool -> bool -> bool -> bool -> R -> Set :=
  | SgrNull of x = 0 : sgr_val x 0 true true true true false false
    true false false true false false 0
  | SgrPos of x > 0 : sgr_val x x false false true false false true
    false false true false false true 1
  | SgrNeg of x < 0 : sgr_val x (- x) false true false false true false
    false true false false true false (-1).

Lemma sgrP x :
  sgr_val x `|x| (0 == x) (x <= 0) (0 <= x) (x == 0) (x < 0) (0 < x)
  (0 == sgr x) (-1 == sgr x) (1 == sgr x)
  (sgr x == 0)  (sgr x == -1) (sgr x == 1) (sgr x).
Proof.
by rewrite ![_ == sgr _]eq_sym !sgr_cp0 /sgr; case: ltrgt0P; constructor.
Qed.

Lemma sgrN x : sgr (-x) = - sgr x.
Proof.
case (ltrgtP x 0)=> hx; last by rewrite hx !(oppr0, sgr0).
  by rewrite gtr0_sg ?oppr_cp0// ltr0_sg// opprK.
by rewrite ltr0_sg ?oppr_cp0// gtr0_sg.
Qed.

Lemma mulr_sg x : sgr x * sgr x = (x != 0)%:R.
Proof. by case: sgrP; rewrite ?(mulr0, mulr1, mulrNN). Qed.

Lemma mulr_sg_eq1 x y : (sgr x * sgr y == 1) = (x != 0) && (sgr x == sgr y).
Proof.
do 2?case: sgrP=> _; rewrite ?(mulr0, mulr1, mulrN1, opprK, oppr0, eqxx);
  by rewrite ?[0 == 1]eq_sym ?oner_eq0 //= eqr_oppC oppr0 oner_eq0.
Qed.

Lemma mulr_sg_eqN1 x y : (sgr x * sgr y == -1) = (x != 0) && (sgr x == - sgr y).
Proof. by rewrite -eqr_oppC -mulrN -sgrN mulr_sg_eq1. Qed.

Lemma normr_dec x : `|x| = sgr x * x.
Proof. by case: sgrP; rewrite ?(mul0r, mul1r, mulN1r). Qed.

Lemma sgrM x y : sgr (x * y) = sgr x * sgr y.
Proof.
have [/eqP|/mulIf] := eqVneq (x * y) 0; last apply.
  by rewrite mulf_eq0 => /orP [] /eqP ->; rewrite !(sgr0, mulr0, mul0r).
by rewrite -normr_dec normrM normr_dec mulrAC normr_dec -!mulrA [y * x]mulrC.
Qed.

Lemma sgrX n x : sgr (x ^+ n) = (sgr x) ^+ n.
Proof. by elim: n => [|n ihn]; rewrite ?sgr1 // !exprS sgrM ihn. Qed.

Lemma sgr_eq0 x : (sgr x == 0) = (x == 0).
Proof. by rewrite sgr_cp0. Qed.

Lemma sgr_odd n x : x != 0 -> (sgr x) ^+ n = (sgr x) ^+ (odd n).
Proof. by case: sgrP=> //=; rewrite ?expr1n // signr_odd. Qed.

Lemma sgrMn x n : sgr (x *+ n) = (n != 0%N)%:R * sgr x.
Proof.
case: n=> [|n]; first by rewrite mulr0n sgr0 mul0r.
by rewrite !sgr_def mulrn_eq0 mul1r pmulrn_llt0.
Qed.
Lemma sgr_nat n : sgr (n%:R) = (n != 0%N)%:R :> R.
Proof. by rewrite sgrMn sgr1 mulr1. Qed.

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

(* normr section *)

Lemma mulr_sg_norm x : sgr x * `|x| = x.
Proof. by case: sgrP; rewrite !(mul1r, mul0r, mulrNN). Qed.

Lemma ler_norml x y : (`|x| <= y) = (-y <= x <= y).
Proof. by rewrite real_ler_norml ?ordered_real. Qed.

Lemma ler_normlP x y : reflect ((-x <= y) * (x <= y)) (`|x| <= y).
Proof. by apply: real_ler_normlP; rewrite ordered_real. Qed.
Implicit Arguments ler_normlP [x y].

Lemma eqr_norml x y : (`|x| == y) = ((x == y) || (x == -y)) && (0 <= y).
Proof. by rewrite real_eqr_norml ?ordered_real. Qed.

Lemma eqr_norm2 x y : (`|x| == `|y|) = (x == y) || (x == -y).
Proof. by rewrite real_eqr_norm2 ?ordered_real. Qed.

Lemma ltr_norml x y : (`|x| < y) = (-y < x < y).
Proof. by rewrite real_ltr_norml ?ordered_real. Qed.

Definition lter_norml := (ler_norml, ltr_norml).

Lemma ltr_normlP x y : reflect ((-x < y) * (x < y)) (`|x| < y).
Proof. by apply: real_ltr_normlP; rewrite ordered_real. Qed.

Implicit Arguments ltr_normlP [x y].

Lemma ler_normr x y : (x <= `|y|) = (x <= y) || (x <= -y).
Proof. by rewrite lerNgt ltr_norml negb_and -!lerNgt orbC ler_oppr. Qed.

Lemma ltr_normr x y : (x < `|y|) = (x < y) || (x < -y).
Proof. by rewrite ltrNge ler_norml negb_and -!ltrNge orbC ltr_oppr. Qed.

Definition lter_normr :=  (ler_normr, ltr_normr).

Lemma ler_nnorml x y (hy : y < 0) : (`|x| <= y = false).
Proof. by apply: negbTE; rewrite -ltrNge (ltr_le_trans hy) ?normrE. Qed.

Lemma ltr_nnorml x y (hy : y <= 0) : (`|x| < y = false).
Proof. by apply: negbTE; rewrite -lerNgt (ler_trans hy) ?normrE. Qed.

Definition lter_nnormr := (ler_nnorml, ltr_nnorml).

Lemma ler_distl x y e : (`|x - y| <= e) = (y - e <= x <= y + e).
Proof. by rewrite lter_norml !lter_sub_addl. Qed.

Lemma ltr_distl x y e : (`|x - y| < e) = (y - e < x < y + e).
Proof. by rewrite lter_norml !lter_sub_addl. Qed.

Definition lter_distl := (ler_distl, ltr_distl).

Lemma normr_sg x : `|sgr x| = (x != 0)%:R.
Proof. by case: sgrP; rewrite ?normrE. Qed.

Lemma sgr_norm x : sgr `|x| = (x != 0)%:R.
Proof. by rewrite normr_dec sgr_smul mulr_sg. Qed.

Lemma exprn_even_ge0 n x : ~~ odd n -> 0 <= x ^+ n.
Proof. by move=> even_n; rewrite real_exprn_even_ge0 ?ordered_real. Qed.

(* particular case for squares *)
Lemma sqr_ge0 (x : R) : 0 <= x ^+ 2. Proof. by rewrite exprn_even_ge0. Qed.

Lemma sqr_norm_eq1 x : (x ^+ 2 == 1) = (`|x| == 1).
Proof. by rewrite sqrf_eq1 eqr_norml ler01 andbT. Qed.

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
Proof. by case: minrP=> hxy; rewrite ?eqxx // ltr_eqF. Qed.

Lemma eqr_minr x y : (minr x y == y) = (y <= x).
Proof. by rewrite minrC eqr_minl. Qed.

Lemma eqr_maxl x y : (maxr x y == x) = (y <= x).
Proof. by case: maxrP=> hxy; rewrite ?eqxx // eq_sym ltr_eqF. Qed.

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
move=> x y z; rewrite -[_ + _]opprK opprD oppr_max.
by rewrite addr_minl -!opprD oppr_min !opprK.
Qed.

Lemma addr_maxr : right_distributive +%R (@maxr R).
Proof.
move=> x y z; rewrite -[_ + _]opprK opprD oppr_max.
by rewrite addr_minr -!opprD oppr_min !opprK.
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
case: ger0P=> hx; first by rewrite maxr_l // ge0_cp //.
by rewrite maxr_r // le0_cp // ltrW.
Qed.

Lemma maxNr x : maxr (- x) x = `|x|.
Proof. by rewrite maxrC maxrN. Qed.

Lemma minrN x : minr x (- x) = - `|x|.
Proof. by rewrite -[minr _ _]opprK oppr_min opprK maxNr. Qed.

Lemma minNr x : minr (- x) x = - `|x|.
Proof. by rewrite -[minr _ _]opprK oppr_min opprK maxrN. Qed.

End MinMax.

End TIntegralDomainOperationTheory.
End TIntegralDomainTheory.

Include TIntegralDomainTheory.

Module TField.

Section ClassDef.

Record class_of R :=
  Class { base : PField.class_of R; mixin : oidom_mixin_of R base }.
Definition base2 R (c : class_of R) := TIntegralDomain.Class (@mixin _ c).
Local Coercion base : class_of >-> PField.class_of.
Local Coercion base2 : class_of >-> TIntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack := gen_pack' Pack Class PField.class.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := PIntegralDomain.Pack (class cT) cT.
Definition oIdomainType cT := TIntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition poFieldType cT := PField.Pack (class cT) cT.
Definition join_poIdomainType cT :=
  @PIntegralDomain.Pack (poFieldType cT) (class cT) cT.
Definition join_oIdomainType cT :=
  @TIntegralDomain.Pack (poFieldType cT) (class cT) cT.
Definition join_fieldType cT :=
  @GRing.Field.Pack (poFieldType cT) (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> PField.class_of.
Coercion base2 : class_of >-> TIntegralDomain.class_of.
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
Coercion poIdomainType : type >-> PIntegralDomain.type.
Canonical poIdomainType.
Coercion oIdomainType : type >-> TIntegralDomain.type.
Canonical oIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion poFieldType : type >-> PField.type.
Canonical poFieldType.

Canonical join_poIdomainType.
Canonical join_oIdomainType.
Canonical join_fieldType.

End Exports.

End TField.
Import TField.Exports.

Module TFieldTheory.

Import PIntegralDomainTheory.
Import PFieldTheory.
Import TIntegralDomainTheory.

Section TFieldTheory.

Variable F : TField.type.
Implicit Types x y z t : F.

Hint Resolve lerr.

Lemma invr_sg x : (sgr x)^-1 = sgr x.
Proof. by case: sgrP; rewrite ?(invr0, invrN, invr1). Qed.

Lemma sgrV x : sgr (x^-1) = sgr x.
Proof. by rewrite /sgr invr_eq0 invr_lt0. Qed.

Local Notation mid x y := ((x + y) / 2%:R).

Lemma midf_le x y (lxy : x <= y) : (x <= mid x y) * (mid x y  <= y).
Proof.
rewrite ler_pdivl_mulr ?ler_pdivr_mulr ?ltr0Sn //.
by rewrite !mulrDr !mulr1 ler_add2r ler_add2l.
Qed.

Lemma midf_lt x y (lxy : x < y) : (x < mid x y) * (mid x y  < y).
Proof.
rewrite ltr_pdivl_mulr ?ltr_pdivr_mulr ?ltr0Sn //.
by rewrite !mulrDr !mulr1 ltr_add2r ltr_add2l.
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

End TFieldTheory.
End TFieldTheory.

Module ArchimedianField.

Section ClassDef.

Record mixin_of (R : PIntegralDomain.type) := Mixin {
  archi_bound : R -> nat;
  _ : forall (x : R), 0 <= x -> x < (archi_bound x)%:R
}.

Record class_of (R : Type) : Type := Class {
  base : TField.class_of R;
  mixin : mixin_of (PIntegralDomain.Pack base R)
}.
Local Coercion base : class_of >-> TField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack T b0 (m0 : mixin_of (@TField.Pack T b0 T)) :=
  fun bT b & phant_id (TField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := PIntegralDomain.Pack (class cT) cT.
Definition oIdomainType cT := TIntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition poFieldType cT := PField.Pack (class cT) cT.
Definition oFieldType cT := TField.Pack (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> TField.class_of.
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
Coercion poIdomainType : type >-> PIntegralDomain.type.
Canonical poIdomainType.
Coercion oIdomainType : type >-> TIntegralDomain.type.
Canonical oIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion poFieldType : type >-> PField.type.
Canonical poFieldType.
Coercion oFieldType : type >-> TField.type.
Canonical oFieldType.
End Exports.

End ArchimedianField.
Import ArchimedianField.Exports.

Definition archi_bound (R : ArchimedianField.type) : R -> nat
  := ArchimedianField.archi_bound
  (ArchimedianField.mixin (ArchimedianField.class R)).

Module ArchimedianFieldTheory.
Import PIntegralDomainTheory.
Import PFieldTheory.
Import TIntegralDomainTheory.
Import TFieldTheory.

Section ArchimedianFieldTheory.
Variable F : ArchimedianField.type.

Lemma archi_boundP (x : F) : 0 <= x -> x < (archi_bound x)%:R.
Proof. by move: x; rewrite /archi_bound; case: ArchimedianField.mixin. Qed.

Lemma upper_nthrootP (x : F) i : (archi_bound x <= i)%N -> x < 2%:R ^+ i.
Proof.
rewrite -(@ler_eexpn2l _ (2%:R : F)) ?ltr1n => // /ltr_le_trans-> //.
have [x_lt0|/archi_boundP /ltr_le_trans-> //] := ltrP x 0.
  by rewrite (ltr_le_trans x_lt0) // exprn_ge0 // ler0n.
rewrite ltrW // -natrX ltr_nat; elim: archi_bound=> // n ihn.
by rewrite expnS mul2n -addnn -addn1 leq_add // (leq_trans _ ihn).
Qed.

End ArchimedianFieldTheory.
End ArchimedianFieldTheory.

Module RealClosedField.

Section ClassDef.

Definition axiom (F : TField.type) := forall (p : {poly F}) (a b : F), a <= b
    -> p.[a] <= 0 <= p.[b] -> { x | a <= x <= b & root p x }.

Record mixin_of (F : TField.type) := Mixin {
  _ : axiom F
}.

Record class_of (R : Type) : Type := Class {
  base : TField.class_of R;
  mixin : mixin_of (TField.Pack base R)
}.
Local Coercion base : class_of >-> TField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.
Definition pack T b0 (m0 : mixin_of (@TField.Pack T b0 T)) :=
  fun bT b & phant_id (TField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType cT := Equality.Pack (class cT) cT.
Definition choiceType cT := Choice.Pack (class cT) cT.
Definition zmodType cT := GRing.Zmodule.Pack (class cT) cT.
Definition ringType cT := GRing.Ring.Pack (class cT) cT.
Definition comRingType cT := GRing.ComRing.Pack (class cT) cT.
Definition unitRingType cT := GRing.UnitRing.Pack (class cT) cT.
Definition comUnitRingType cT := GRing.ComUnitRing.Pack (class cT) cT.
Definition idomainType cT := GRing.IntegralDomain.Pack (class cT) cT.
Definition poIdomainType cT := PIntegralDomain.Pack (class cT) cT.
Definition oIdomainType cT := TIntegralDomain.Pack (class cT) cT.
Definition fieldType cT := GRing.Field.Pack (class cT) cT.
Definition poFieldType cT := PField.Pack (class cT) cT.
Definition oFieldType cT := TField.Pack (class cT) cT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> TField.class_of.
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
Coercion poIdomainType : type >-> PIntegralDomain.type.
Canonical poIdomainType.
Coercion oIdomainType : type >-> TIntegralDomain.type.
Canonical oIdomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion poFieldType : type >-> PField.type.
Canonical poFieldType.
Coercion oFieldType : type >-> TField.type.
Canonical oFieldType.
End Exports.

End RealClosedField.
Import RealClosedField.Exports.

Module RealClosedFieldTheory.
Import PIntegralDomainTheory.
Import PFieldTheory.
Import TIntegralDomainTheory.
Import TFieldTheory.

Section RealClosedFieldTheory.
Variable R : RealClosedField.type.

Lemma poly_ivt : RealClosedField.axiom R.
Proof. by move: R=> [? [? []]]. Qed.

(* Square Root theory *)

Lemma sqrtr_subproof (x : R) :
  {y | (0 <= y) && if 0 <= x then (y ^+ 2 == x) else y == 0}.
Proof.
have [x_ge0|] := ger0P x; last by exists 0; rewrite lerr eqxx.
have [] := @poly_ivt ('X^2 - x%:P) 0 (x + 1).
* by rewrite ler_paddr ?ler01.
* rewrite !hornerD !hornerN !horner_exp !hornerC !hornerX.
  rewrite exprS mul0r sub0r oppr_le0 x_ge0 /= sqrrD1 -!addrA.
  by rewrite addr_ge0 ?mulr_ge0 // addrCA subrr addr0 addr_ge0 ?ler01.
move=> y /andP[y_ge0 _]; rewrite /root !hornerE subr_eq0.
by move/eqP <-; exists y; rewrite y_ge0 eqxx.
Qed.

Definition sqrtr (a : R) : R := projT1 (sqrtr_subproof a).

Lemma sqrtr_ge0 a : 0 <= sqrtr a.
Proof. by rewrite /sqrtr; case: sqrtr_subproof => x /= /andP []. Qed.
Hint Resolve sqrtr_ge0.

Lemma sqr_sqrtr a : 0 <= a -> (sqrtr a)^+2 = a.
Proof.
move=> a_ge0; rewrite /sqrtr; case: sqrtr_subproof.
by move=> x /= /andP [_]; rewrite a_ge0 => /eqP.
Qed.

Lemma ler0_sqrtr a : a <= 0 -> sqrtr a = 0.
Proof.
rewrite /sqrtr; case: sqrtr_subproof => x /=.
have [//|_ /andP [_ /eqP] //|->] := ltrgt0P a.
by rewrite mulf_eq0 orbb => /andP [_ /eqP].
Qed.

Lemma ltr0_sqrtr a : a < 0 -> sqrtr a = 0.
Proof. by move=> /ltrW; apply: ler0_sqrtr. Qed.

CoInductive sqrtr_spec (a : R) : R -> bool -> bool -> R -> Type :=
| IsNoSqrtr of a < 0 : sqrtr_spec a a false true 0
| IsSqrtr b of 0 <= b : sqrtr_spec a (b ^+ 2) true false b.

Lemma sqrtrP a : sqrtr_spec a a (0 <= a) (a < 0) (sqrtr a).
Proof.
have [a_ge0|a_lt0] := ger0P a.
  by rewrite -{1 2}[a]sqr_sqrtr //; constructor.
by rewrite ltr0_sqrtr //; constructor.
Qed.

(* move to orderedalg for any oIdomainType of with precondition a \in real *)

Lemma sqrtr_sqr a : sqrtr (a ^+ 2) = `|a|.
Proof.
have /eqP : sqrtr (a ^+ 2) ^+2 = `|a| ^+ 2.
  by rewrite -normrX ger0_norm ?sqr_sqrtr ?sqr_ge0.
rewrite -subr_eq0 subr_sqr mulf_eq0 subr_eq0 addr_eq0 => /orP [/eqP-> //|ha].
have := sqrtr_ge0 (a ^+ 2); rewrite (eqP ha) oppr_ge0 normr_le0 => /eqP ->.
by rewrite normr0 oppr0.
Qed.

Lemma sqrtrM a b : 0 <= a -> 0 <= b ->
  sqrtr (a * b) = sqrtr a * sqrtr b.
Proof.
case: (sqrtrP a) => // {a} a a_ge0; case: (sqrtrP b) => // {b} b b_ge0 _ _.
by rewrite mulrMM sqrtr_sqr ger0_norm ?mulr_ge0.
Qed.

Lemma sqrtr0 : sqrtr 0 = 0.
Proof. by move: (sqrtr_sqr 0); rewrite exprS mul0r => ->; rewrite normr0. Qed.

Lemma sqrtr1 : sqrtr 1 = 1.
Proof. by move: (sqrtr_sqr 1); rewrite expr1n => ->; rewrite normr1. Qed.

Lemma sqrtr_eq0 a : (sqrtr a == 0) = (a <= 0).
Proof.
case: sqrtrP => [/ltrW ->|b]; first by rewrite eqxx.
case: ltrgt0P => [b_gt0|//|->]; last by rewrite exprS mul0r lerr.
by rewrite ltr_geF ?pmulr_rgt0.
Qed.

Lemma sqrtr_gt0 a : (0 < sqrtr a) = (0 < a).
Proof. by rewrite lt0r sqrtr_ge0 sqrtr_eq0 -ltrNge andbT. Qed.

Lemma eqr_sqrt (a b : R) : 0 <= a -> 0 <= b ->
  (sqrtr a == sqrtr b) = (a == b).
Proof.
move=> a_ge0 b_ge0; apply/eqP/eqP=> [HS|->] //.
by move: (sqr_sqrtr a_ge0); rewrite HS (sqr_sqrtr b_ge0).
Qed.

Lemma ler_wsqrtr : {homo sqrtr : a b / a <= b}.
Proof.
move=> a b /= le_ab; case: (boolP (0 <= a))=> [pa|]; last first.
  by rewrite -ltrNge; move/ltrW; rewrite -sqrtr_eq0; move/eqP->.
rewrite -(@ler_pexpn2r R 2) -?topredE /= ?sqrtr_ge0 //.
by rewrite !sqr_sqrtr // (ler_trans pa).
Qed.

Lemma ler_psqrt : {in >%R 0 &, {mono sqrtr : a b / a <= b}}.
Proof.
apply: homo_mono_in => x y; rewrite -!topredE /= => x_gt0 y_gt0.
rewrite !ltr_neqAle => /andP [neq_xy le_xy].
by rewrite ler_wsqrtr // eqr_sqrt ?ltrW // neq_xy.
Qed.

Lemma ler_sqrt a b : 0 < b -> (sqrtr a <= sqrtr b) = (a <= b).
Proof.
move=> b_gt0; have [a_le0|a_gt0] := ler0P a; last by rewrite ler_psqrt.
by rewrite ler0_sqrtr // sqrtr_ge0 (ler_trans a_le0) ?ltrW.
Qed.

Lemma ltr_sqrt a b : 0 < b -> (sqrtr a < sqrtr b) = (a < b).
Proof.
move=> b_gt0; have [a_le0|a_gt0] := ler0P a; last first.
  by rewrite (lerW_mono_in ler_psqrt).
by rewrite ler0_sqrtr // sqrtr_gt0 b_gt0 (ler_lt_trans a_le0).
Qed.

End RealClosedFieldTheory.
End RealClosedFieldTheory.
Include RealClosedFieldTheory.

Module Theory.
Export PIntegralDomainTheory.
Export PFieldTheory.
Export TIntegralDomainTheory.
Export TFieldTheory.
Export ArchimedianFieldTheory.
Export RealClosedFieldTheory.

Hint Resolve @ler01.
Implicit Arguments ler01 [R].
Hint Resolve lerr.
Hint Resolve @ltr01.
Implicit Arguments ltr01 [R].
Hint Resolve ltrr.
Hint Resolve ltrW.
Hint Resolve ltr_eqF.
Hint Resolve ltr0Sn.
Hint Resolve ler0n.
Hint Resolve normr_ge0.
Hint Resolve ler_opp2.
Hint Resolve ordered_real.

End Theory.

End ORing.

Export ORing.PIntegralDomain.Exports.
Export ORing.PField.Exports.
Export ORing.ClosedField.Exports.
Export ORing.TIntegralDomain.Exports.
Export ORing.TField.Exports.
Export ORing.ArchimedianField.Exports.
Export ORing.RealClosedField.Exports.

Notation PartialOrderMixin := ORing.Mixin.
(* Notation PartialOrderLeMixin := ORing.LeMixin. *)
(* Notation PartialOrderLtMixin := ORing.LtMixin. *)
(* Notation PartialOrderPosMixin := ORing.PosMixin. *)
(* Notation PartialOrderNonNegMixin := ORing.NonNegMixin. *)

Notation TotalPartialLeMixin := ORing.TotalPLeMixin.
Notation TotalPartialLtMixin := ORing.TotalPLtMixin.
(* Notation TotalOrder_PartialPosMixin := ORing.TotalPPosMixin. *)
(* Notation TotalOrder_PartialNonNegMixin := ORing.TotalPNonNegMixin. *)

Notation TotalLeMixin := ORing.le_total.
Notation TotalLtMixin := ORing.TLtMixin.
(* Notation TotalOrderPosMixin := ORing.TPosMixin. *)
(* Notation TotalOrderNonNegMixin := ORing.TNonNegMixin. *)

Notation ArchimedianMixin := ORing.ArchimedianField.Mixin.
Notation RcfMixin := ORing.RealClosedField.Mixin.

Notation poIdomainType := ORing.PIntegralDomain.type.
Notation poFieldType := ORing.PField.type.
Notation poClosedFieldType := ORing.ClosedField.type.
Notation oIdomainType := ORing.TIntegralDomain.type.
Notation oFieldType := ORing.TField.type.
Notation archiFieldType := ORing.ArchimedianField.type.
Notation rcfType := ORing.RealClosedField.type.

Notation POIdomainType T m :=
  (@ORing.PIntegralDomain.pack T _ m _ _ id _ id).
Notation POFieldType T m :=
  (@ORing.PField.pack T _ m _ _ id _ id).
Notation POClosedFieldType T m :=
  (@ORing.ClosedField.pack T _ m _ _ id _ id).
Notation OIdomainType T m :=
  (@ORing.TIntegralDomain.pack T _ m _ _ id _ id).
Notation OFieldType T m :=
  (@ORing.TField.pack T _ m _ _ id _ id).
Notation ArchiFieldType T m :=
  (@ORing.ArchimedianField.pack T _ m _ _ id _ id).
Notation RcfType T m :=
  (@ORing.RealClosedField.pack T _ m _ _ id _ id).

Notation "[ 'poIdomainType' 'of' T ]" :=
    (@ORing.PIntegralDomain.clone T _ _ id)
  (at level 0, format "[ 'poIdomainType'  'of'  T ]") : form_scope.
Notation "[ 'poFieldType' 'of' T ]" :=
  (@ORing.PField.clone T _ _ id)
  (at level 0, format "[ 'poFieldType'  'of'  T ]") : form_scope.
Notation "[ 'poClosedFieldType' 'of' T ]" :=
  (@ORing.ClosedField.clone T _ _ id)
  (at level 0, format "[ 'poClosedFieldType'  'of'  T ]") : form_scope.
Notation "[ 'oIdomainType' 'of' T ]" :=
    (@ORing.TIntegralDomain.clone T _ _ id)
  (at level 0, format "[ 'oIdomainType'  'of'  T ]") : form_scope.
Notation "[ 'oFieldType' 'of' T ]" :=
  (@ORing.TField.clone T _ _ id)
  (at level 0, format "[ 'oFieldType'  'of'  T ]") : form_scope.
Notation "[ 'archiFieldType' 'of' T ]" :=
  (@ORing.ArchimedianField.clone T _ _ id)
  (at level 0, format "[ 'archiFieldType'  'of'  T ]") : form_scope.
Notation "[ 'rcfType' 'of' T ]" :=
  (@ORing.RealClosedField.clone T _ _ id)
  (at level 0, format "[ 'rcfType'  'of'  T ]") : form_scope.

Notation rcf_axiom := (@ORing.RealClosedField.axiom).
Notation archi_bound := (@ORing.archi_bound _).

Notation ">=%R" := (@ORing.OrderDef.ler _) : ring_scope.
Notation "x <= y" := (ORing.OrderDef.ler x y) : ring_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T))
  (at level 70, y at next level) : ring_scope.
Notation "x >= y" := (y <= x) (only parsing) : ring_scope.
Notation "x >= y :> T" := ((x : T) >= (y : T))
  (at level 70, y at next level, only parsing) : ring_scope.
Notation "<=%R" := [rel x y | y <= x] : ring_scope.

Notation ">%R" := (@ORing.OrderDef.ltr _) : ring_scope.
Notation "x < y"  := (ORing.OrderDef.ltr x y) : ring_scope.
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

Notation "<?=%R" := (@ORing.OrderDef.lerif _) : ring_scope.
Notation "x <= y ?= 'iff' c" := (ORing.OrderDef.lerif x y c) : ring_scope.
Notation "x <= y ?= 'iff' c :> R" := ((x : R) <= (y : R) ?= iff c) : ring_scope.

Coercion ler_of_leif (R : poIdomainType)
  (x y : R) c (le_xy : x <= y ?= iff c) := le_xy.1 : x <= y.

(* Module NormrNotation. *)
Notation "`| x |" := (ORing.OrderDef.normr x) : ring_scope.
(* End NormrNotation. *)

